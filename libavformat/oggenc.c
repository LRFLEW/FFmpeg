/*
 * Ogg muxer
 * Copyright (c) 2007 Baptiste Coudurier <baptiste dot coudurier at free dot fr>
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include <stdint.h>

#include "libavutil/base64.h"
#include "libavutil/crc.h"
#include "libavutil/mathematics.h"
#include "libavutil/opt.h"
#include "libavutil/random_seed.h"
#include "libavcodec/xiph.h"
#include "libavcodec/bytestream.h"
#include "libavcodec/flac.h"
#include "avformat.h"
#include "avio_internal.h"
#include "flac_picture.h"
#include "internal.h"
#include "vorbiscomment.h"

#define MAX_PAGE_SIZE 65025

typedef struct OGGPage {
    int64_t start_granule;
    int64_t granule;
    int stream_index;
    uint8_t flags;
    uint8_t segments_count;
    uint8_t segments[255];
    uint8_t data[MAX_PAGE_SIZE];
    uint16_t size;
} OGGPage;

typedef struct OGGPageList {
    OGGPage page;
    struct OGGPageList *next;
} OGGPageList;

typedef struct OGGStreamContext {
    unsigned page_counter;
    uint8_t *header[3];
    int header_len[3];
    /** for theora granule */
    int kfgshift;
    int64_t last_kf_pts;
    int vrev;
    /* for VP8 granule */
    int isvp8;
    int eos;
    unsigned page_count; ///< number of page buffered
    OGGPage page; ///< current page
    unsigned serial_num; ///< serial number
    int64_t last_granule; ///< last packet granule
    /* for embeded pictures */
    OGGPageList *comments;
    unsigned int attach_count;
    unsigned attached_types;
} OGGStreamContext;

typedef struct OGGAttachContext {
    int attach_to;
    unsigned int count;
} OGGAttachContext;

typedef struct OGGContext {
    const AVClass *class;
    OGGPageList *page_list;
    int pref_size; ///< preferred page size (0 => fill all segments)
    int64_t pref_duration;      ///< preferred page duration (0 => fill all segments)
    int serial_offset;
    unsigned int attach_count;
} OGGContext;

#define OFFSET(x) offsetof(OGGContext, x)
#define PARAM AV_OPT_FLAG_ENCODING_PARAM

static const AVOption options[] = {
    { "serial_offset", "serial number offset",
        OFFSET(serial_offset), AV_OPT_TYPE_INT, { .i64 = 0 }, 0, INT_MAX, PARAM },
    { "oggpagesize", "Set preferred Ogg page size.",
      OFFSET(pref_size), AV_OPT_TYPE_INT, {.i64 = 0}, 0, MAX_PAGE_SIZE, PARAM},
    { "pagesize", "preferred page size in bytes (deprecated)",
        OFFSET(pref_size), AV_OPT_TYPE_INT, { .i64 = 0 }, 0, MAX_PAGE_SIZE, PARAM },
    { "page_duration", "preferred page duration, in microseconds",
        OFFSET(pref_duration), AV_OPT_TYPE_INT64, { .i64 = 1000000 }, 0, INT64_MAX, PARAM },
    { NULL },
};

#define OGG_CLASS(flavor, name)\
static const AVClass flavor ## _muxer_class = {\
    .class_name = #name " muxer",\
    .item_name  = av_default_item_name,\
    .option     = options,\
    .version    = LIBAVUTIL_VERSION_INT,\
};

static void ogg_write_page(AVFormatContext *s, OGGPage *page, int extra_flags)
{
    OGGStreamContext *oggstream = s->streams[page->stream_index]->priv_data;
    uint8_t buf[4 + 1 + 1 + 8 + 4 + 4 + 4 + 1 + 255], *ptr = buf, *crc_pos;
    const AVCRC *crc_table = av_crc_get_table(AV_CRC_32_IEEE);
    uint32_t crc;

    bytestream_put_le32(&ptr, MKTAG('O', 'g', 'g', 'S'));
    bytestream_put_byte(&ptr, 0);
    bytestream_put_byte(&ptr, page->flags | extra_flags);
    bytestream_put_le64(&ptr, page->granule);
    bytestream_put_le32(&ptr, oggstream->serial_num);
    bytestream_put_le32(&ptr, oggstream->page_counter++);
    crc_pos = ptr;
    bytestream_put_le32(&ptr, 0);
    bytestream_put_byte(&ptr, page->segments_count);
    bytestream_put_buffer(&ptr, page->segments, page->segments_count);

    crc = av_crc(crc_table, 0, buf, ptr - buf);
    crc = av_crc(crc_table, crc, page->data, page->size);
    bytestream_put_be32(&crc_pos, crc);

    avio_write(s->pb, buf, ptr - buf);
    avio_write(s->pb, page->data, page->size);
    avio_write_marker(s->pb, AV_NOPTS_VALUE, AVIO_DATA_MARKER_FLUSH_POINT);
    oggstream->page_count--;
}

static int ogg_key_granule(OGGStreamContext *oggstream, int64_t granule)
{
    return (oggstream->kfgshift && !(granule & ((1<<oggstream->kfgshift)-1))) ||
           (oggstream->isvp8    && !((granule >> 3) & 0x07ffffff));
}

static int64_t ogg_granule_to_timestamp(OGGStreamContext *oggstream, int64_t granule)
{
    if (oggstream->kfgshift)
        return (granule>>oggstream->kfgshift) +
            (granule & ((1<<oggstream->kfgshift)-1));
    else if (oggstream->isvp8)
        return granule >> 32;
    else
        return granule;
}

static int ogg_compare_granule(AVFormatContext *s, OGGPage *next, OGGPage *page)
{
    AVStream *st2 = s->streams[next->stream_index];
    AVStream *st  = s->streams[page->stream_index];
    int64_t next_granule, cur_granule;

    if (next->granule == -1 || page->granule == -1)
        return 0;

    next_granule = av_rescale_q(ogg_granule_to_timestamp(st2->priv_data, next->granule),
                                st2->time_base, AV_TIME_BASE_Q);
    cur_granule  = av_rescale_q(ogg_granule_to_timestamp(st->priv_data, page->granule),
                                st ->time_base, AV_TIME_BASE_Q);
    return next_granule > cur_granule;
}

static int ogg_reset_cur_page(OGGStreamContext *oggstream)
{
    oggstream->page.granule = -1;
    oggstream->page.flags = 0;
    oggstream->page.segments_count = 0;
    oggstream->page.size = 0;
    return 0;
}

static int ogg_buffer_page(AVFormatContext *s, OGGStreamContext *oggstream, OGGPageList **page)
{
    OGGContext *ogg = s->priv_data;
    OGGPageList **p = &ogg->page_list;
    OGGPageList *l = av_mallocz(sizeof(*l));

    if (!l)
        return AVERROR(ENOMEM);
    l->page = oggstream->page;

    oggstream->page.start_granule = ogg_granule_to_timestamp(oggstream, oggstream->page.granule);
    oggstream->page_count++;
    ogg_reset_cur_page(oggstream);

    while (*p) {
        if (ogg_compare_granule(s, &(*p)->page, &l->page))
            break;
        p = &(*p)->next;
    }
    l->next = *p;
    *p = l;
    if (page) *page = l;

    return 0;
}

static int ogg_buffer_data(AVFormatContext *s, AVStream *st,
                           uint8_t *data, unsigned size, int64_t granule,
                           int header)
{
    OGGStreamContext *oggstream = st->priv_data;
    OGGContext *ogg = s->priv_data;
    int total_segments = size / 255 + 1;
    uint8_t *p = data;
    int i, segments, len, flush = 0;

    // Handles VFR by flushing page because this frame needs to have a timestamp
    // For theora and VP8, keyframes also need to have a timestamp to correctly mark
    // them as such, otherwise seeking will not work correctly at the very
    // least with old libogg versions.
    // Do not try to flush header packets though, that will create broken files.
    if ((st->codecpar->codec_id == AV_CODEC_ID_THEORA || st->codecpar->codec_id == AV_CODEC_ID_VP8) && !header &&
        (ogg_granule_to_timestamp(oggstream, granule) >
         ogg_granule_to_timestamp(oggstream, oggstream->last_granule) + 1 ||
         ogg_key_granule(oggstream, granule))) {
        if (oggstream->page.granule != -1)
            ogg_buffer_page(s, oggstream, NULL);
        flush = 1;
    }

    // avoid a continued page
    if (!header && oggstream->page.size > 0 &&
        MAX_PAGE_SIZE - oggstream->page.size < size) {
        ogg_buffer_page(s, oggstream, NULL);
    }

    for (i = 0; i < total_segments; ) {
        OGGPage *page = &oggstream->page;

        segments = FFMIN(total_segments - i, 255 - page->segments_count);

        if (i && !page->segments_count)
            page->flags |= 1; // continued packet

        memset(page->segments+page->segments_count, 255, segments - 1);
        page->segments_count += segments - 1;

        len = FFMIN(size, segments*255);
        page->segments[page->segments_count++] = len - (segments-1)*255;
        memcpy(page->data+page->size, p, len);
        p += len;
        size -= len;
        i += segments;
        page->size += len;

        if (i == total_segments)
            page->granule = granule;

        {
            AVStream *st = s->streams[page->stream_index];

            int64_t start = av_rescale_q(page->start_granule, st->time_base,
                                         AV_TIME_BASE_Q);
            int64_t next  = av_rescale_q(ogg_granule_to_timestamp(oggstream, page->granule),
                                         st->time_base, AV_TIME_BASE_Q);

            if (page->segments_count == 255) {
                ogg_buffer_page(s, oggstream, NULL);
            } else if (!header) {
                if ((ogg->pref_size     > 0 && page->size   >= ogg->pref_size) ||
                    (ogg->pref_duration > 0 && next - start >= ogg->pref_duration)) {
                    ogg_buffer_page(s, oggstream, NULL);
                }
            }
        }
    }

    if (flush && oggstream->page.granule != -1)
        ogg_buffer_page(s, oggstream, NULL);

    return 0;
}

static int ogg_append_page(AVFormatContext *s, OGGPageList **page_list,
                           uint8_t *data, unsigned size, int new_packet)
{
    int append, seg_size = 255, started = 0;
    OGGPage *p = &(*page_list)->page;
    int64_t granule = p->granule;

    if (!new_packet) {
        p->granule = -1;
        append = FFMIN(255 - p->segments[p->segments_count - 1], size);
        memcpy(p->data + p->size, data, append);
        p->size += append;
        seg_size = (p->segments[p->segments_count - 1] += append);
        data += append;
        size -= append;
        started = 1;
    }

    while (size > 0 || seg_size == 255) {
        if (p->segments_count == 255) {
            OGGPageList *new_page = av_malloc(sizeof(OGGPageList));
            if (!new_page)
                return AVERROR(ENOMEM);
            new_page->page = (OGGPage) {
                .start_granule = p->start_granule,
                .granule = -1,
                .stream_index = p->stream_index,
                .flags = started,
                .segments_count = 0,
                .size = 0,
            };
            new_page->next = (*page_list)->next;
            (*page_list)->next = new_page;
            (*page_list) = new_page;
            p = &new_page->page;
            ((OGGStreamContext *) s->streams[p->stream_index]->priv_data)->page_count++;
        }

        seg_size = FFMIN(255, size);
        memcpy(p->data + p->size, data, seg_size);
        p->size += seg_size;
        p->segments[p->segments_count++] = seg_size;
        data += seg_size;
        size -= seg_size;
        started = 1;
    }

    p->granule = granule;
    return 0;
}

static uint8_t *ogg_write_vorbiscomment(int64_t offset, int bitexact,
                                        int *header_len, AVDictionary **m, int framing_bit,
                                        AVChapter **chapters, unsigned int nb_chapters,
                                        unsigned int nb_attach)
{
    const char *vendor = bitexact ? "ffmpeg" : LIBAVFORMAT_IDENT;
    AVIOContext pb;
    int64_t comment_size, size;
    uint8_t *p;

    ff_metadata_conv(m, ff_vorbiscomment_metadata_conv, NULL);

    comment_size = ff_vorbiscomment_length(*m, vendor, chapters, nb_chapters);
    size = offset + comment_size + framing_bit;
    if (size > INT_MAX)
        return NULL;
    p = av_mallocz(size);
    if (!p)
        return NULL;

    ffio_init_context(&pb, p + offset, size - offset, 1, NULL, NULL, NULL, NULL);
    ff_vorbiscomment_write(&pb, *m, vendor, chapters, nb_chapters, nb_attach);
    if (framing_bit)
        avio_w8(&pb, 1);

    *header_len = size;
    return p;
}

static int ogg_build_flac_headers(AVCodecParameters *par,
                                  OGGStreamContext *oggstream, int bitexact,
                                  AVDictionary **m)
{
    uint8_t *p;

    if (par->extradata_size < FLAC_STREAMINFO_SIZE)
        return AVERROR(EINVAL);

    // first packet: STREAMINFO
    oggstream->header_len[0] = 51;
    oggstream->header[0] = av_mallocz(51); // per ogg flac specs
    p = oggstream->header[0];
    if (!p)
        return AVERROR(ENOMEM);
    bytestream_put_byte(&p, 0x7F);
    bytestream_put_buffer(&p, "FLAC", 4);
    bytestream_put_byte(&p, 1); // major version
    bytestream_put_byte(&p, 0); // minor version
    bytestream_put_be16(&p, 1 + oggstream->attach_count); // headers packets without this one
    bytestream_put_buffer(&p, "fLaC", 4);
    bytestream_put_byte(&p, 0x00); // streaminfo
    bytestream_put_be24(&p, 34);
    bytestream_put_buffer(&p, par->extradata, FLAC_STREAMINFO_SIZE);

    // second packet: VorbisComment
    p = ogg_write_vorbiscomment(4, bitexact, &oggstream->header_len[1], m, 0, NULL, 0, 0);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[1] = p;
    if (!oggstream->attach_count)
        bytestream_put_byte(&p, 0x84); // last metadata block and vorbis comment
    else
        bytestream_put_byte(&p, 0x04); // vorbis comment followed by attachments
    bytestream_put_be24(&p, oggstream->header_len[1] - 4);

    return 0;
}

#define SPEEX_HEADER_SIZE 80

static int ogg_build_speex_headers(AVCodecParameters *par,
                                   OGGStreamContext *oggstream, int bitexact,
                                   AVDictionary **m)
{
    uint8_t *p;

    if (par->extradata_size < SPEEX_HEADER_SIZE)
        return AVERROR_INVALIDDATA;

    // first packet: Speex header
    p = av_mallocz(SPEEX_HEADER_SIZE);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[0] = p;
    oggstream->header_len[0] = SPEEX_HEADER_SIZE;
    bytestream_put_buffer(&p, par->extradata, SPEEX_HEADER_SIZE);
    AV_WL32(&oggstream->header[0][68], 0);  // set extra_headers to 0

    // second packet: VorbisComment
    p = ogg_write_vorbiscomment(0, bitexact, &oggstream->header_len[1], m, 0,
                                NULL, 0, oggstream->attach_count);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[1] = p;

    return 0;
}

#define OPUS_HEADER_SIZE 19

static int ogg_build_opus_headers(AVCodecParameters *par,
                                  OGGStreamContext *oggstream, int bitexact,
                                  AVDictionary **m, AVChapter **chapters,
                                  unsigned int nb_chapters)
{
    uint8_t *p;

    if (par->extradata_size < OPUS_HEADER_SIZE)
        return AVERROR_INVALIDDATA;

    /* first packet: Opus header */
    p = av_mallocz(par->extradata_size);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[0] = p;
    oggstream->header_len[0] = par->extradata_size;
    bytestream_put_buffer(&p, par->extradata, par->extradata_size);

    /* second packet: VorbisComment */
    p = ogg_write_vorbiscomment(8, bitexact, &oggstream->header_len[1], m, 0,
                                chapters, nb_chapters, oggstream->attach_count);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[1] = p;
    bytestream_put_buffer(&p, "OpusTags", 8);

    return 0;
}

#define VP8_HEADER_SIZE 26

static int ogg_build_vp8_headers(AVFormatContext *s, AVStream *st,
                                 OGGStreamContext *oggstream, int bitexact)
{
    AVCodecParameters *par = st->codecpar;
    uint8_t *p;

    /* first packet: VP8 header */
    p = av_mallocz(VP8_HEADER_SIZE);
    if (!p)
        return AVERROR(ENOMEM);
    oggstream->header[0] = p;
    oggstream->header_len[0] = VP8_HEADER_SIZE;
    bytestream_put_byte(&p, 0x4f); // HDRID
    bytestream_put_buffer(&p, "VP80", 4); // Identifier
    bytestream_put_byte(&p, 1); // HDRTYP
    bytestream_put_byte(&p, 1); // VMAJ
    bytestream_put_byte(&p, 0); // VMIN
    bytestream_put_be16(&p, par->width);
    bytestream_put_be16(&p, par->height);
    bytestream_put_be24(&p, par->sample_aspect_ratio.num);
    bytestream_put_be24(&p, par->sample_aspect_ratio.den);
    if (st->r_frame_rate.num > 0 && st->r_frame_rate.den > 0) {
        // OggVP8 requires pts to increase by 1 per visible frame, so use the least common
        // multiple framerate if available.
        av_log(s, AV_LOG_DEBUG, "Changing time base from %d/%d to %d/%d\n",
               st->time_base.num, st->time_base.den,
               st->r_frame_rate.den, st->r_frame_rate.num);
        avpriv_set_pts_info(st, 64, st->r_frame_rate.den, st->r_frame_rate.num);
    }
    bytestream_put_be32(&p, st->time_base.den);
    bytestream_put_be32(&p, st->time_base.num);

    /* optional second packet: VorbisComment */
    if (av_dict_get(st->metadata, "", NULL, AV_DICT_IGNORE_SUFFIX) || oggstream->attach_count) {
        p = ogg_write_vorbiscomment(7, bitexact, &oggstream->header_len[1], &st->metadata, 0,
                                    NULL, 0, oggstream->attach_count);
        if (!p)
            return AVERROR(ENOMEM);
        oggstream->header[1] = p;
        bytestream_put_byte(&p, 0x4f); // HDRID
        bytestream_put_buffer(&p, "VP80", 4); // Identifier
        bytestream_put_byte(&p, 2); // HDRTYP
        bytestream_put_byte(&p, 0x20);
    }

    oggstream->isvp8 = 1;

    return 0;
}

static void ogg_write_pages(AVFormatContext *s, int flush)
{
    OGGContext *ogg = s->priv_data;
    OGGPageList *next, *p;

    if (!ogg->page_list)
        return;

    for (p = ogg->page_list; p; ) {
        OGGStreamContext *oggstream =
            s->streams[p->page.stream_index]->priv_data;
        if (oggstream->page_count < 2 && !flush)
            break;
        ogg_write_page(s, &p->page,
                       flush == 1 && oggstream->page_count == 1 ? 4 : 0); // eos
        next = p->next;
        av_freep(&p);
        p = next;
    }
    ogg->page_list = p;
}

static int ogg_init(AVFormatContext *s)
{
    OGGContext *ogg = s->priv_data;
    OGGStreamContext *oggstream = NULL;
    OGGAttachContext *attachstream = NULL;
    AVDictionaryEntry *e;
    AVStream *st;
    int attached, i, j, k = 0;
    unsigned serial_num;

    if (ogg->pref_size)
        av_log(s, AV_LOG_WARNING, "The pagesize option is deprecated\n");

    // init stream priv_data
    for (i = 0; i < s->nb_streams; i++) {
        st = s->streams[i];
        if (st->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;

        if (st->codecpar->codec_id != AV_CODEC_ID_VORBIS &&
            st->codecpar->codec_id != AV_CODEC_ID_THEORA &&
            st->codecpar->codec_id != AV_CODEC_ID_SPEEX  &&
            st->codecpar->codec_id != AV_CODEC_ID_FLAC   &&
            st->codecpar->codec_id != AV_CODEC_ID_OPUS   &&
            st->codecpar->codec_id != AV_CODEC_ID_VP8) {
            av_log(s, AV_LOG_ERROR, "Unsupported codec id in stream %d\n", i);
            return AVERROR(EINVAL);
        }

        oggstream = av_mallocz(sizeof(*oggstream));
        if (!oggstream)
            return AVERROR(ENOMEM);
        st->priv_data = oggstream;
    }

    // setup attachment association
    for (i = 0; i < s->nb_streams; i++) {
        st = s->streams[i];
        if (!(st->disposition & AV_DISPOSITION_ATTACHED_PIC))
            continue;
        ogg->attach_count++;

        if (st->codecpar->codec_id != AV_CODEC_ID_GIF &&
            st->codecpar->codec_id != AV_CODEC_ID_MJPEG &&
            st->codecpar->codec_id != AV_CODEC_ID_PNG &&
            st->codecpar->codec_id != AV_CODEC_ID_TIFF &&
            st->codecpar->codec_id != AV_CODEC_ID_BMP) {
            av_log(s, AV_LOG_ERROR, "Unsupported attachment codec id in stream %d\n", i);
            return AVERROR(EINVAL);
        }

        attachstream = av_mallocz(sizeof(*attachstream));
        if (!attachstream)
            return AVERROR(ENOMEM);
        st->priv_data = attachstream;

        attached = 0;
        e = av_dict_get(st->metadata, "ogg_attach", NULL, 0);
        if (e) {
            int ogg_attach = -1;
            int res = sscanf(e->value, "%d", &ogg_attach);
            if (res > 0 && ogg_attach >= 0 && ogg_attach < s->nb_streams &&
                !(s->streams[ogg_attach]->disposition & AV_DISPOSITION_ATTACHED_PIC)) {
                attachstream->attach_to = ogg_attach;
                oggstream = s->streams[ogg_attach]->priv_data;
                oggstream->attach_count++;
                attached = 1;
            }
        }

        for (j = 0; !attached && j < s->nb_streams; ++j) {
            if (!(s->streams[j]->disposition & AV_DISPOSITION_ATTACHED_PIC)) {
                attachstream->attach_to = j;
                oggstream = s->streams[j]->priv_data;
                oggstream->attach_count++;
                attached = 1;
            }
        }
        if (!attached) {
            av_log(s, AV_LOG_ERROR, "Cannot add attachment %d without an audio/video stream\n", i);
            return AVERROR(EINVAL);
        }
    }

    for (i = 0; i < s->nb_streams; i++) {
        st = s->streams[i];
        if (st->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;

        serial_num = k++ + ogg->serial_offset;

        if (st->codecpar->codec_type == AVMEDIA_TYPE_AUDIO) {
            if (st->codecpar->codec_id == AV_CODEC_ID_OPUS)
                /* Opus requires a fixed 48kHz clock */
                avpriv_set_pts_info(st, 64, 1, 48000);
            else
                avpriv_set_pts_info(st, 64, 1, st->codecpar->sample_rate);
        }

        if ((!st->codecpar->extradata || !st->codecpar->extradata_size) &&
            st->codecpar->codec_id != AV_CODEC_ID_VP8) {
            av_log(s, AV_LOG_ERROR, "No extradata present\n");
            return AVERROR_INVALIDDATA;
        }
        oggstream = st->priv_data;

        oggstream->page.stream_index = i;

        if (!(s->flags & AVFMT_FLAG_BITEXACT))
            do {
                serial_num = av_get_random_seed();
                for (j = 0; j < i; j++) {
                    OGGStreamContext *sc = s->streams[j]->priv_data;
                    if (serial_num == sc->serial_num)
                        break;
                }
            } while (j < i);
        oggstream->serial_num = serial_num;

        av_dict_copy(&st->metadata, s->metadata, AV_DICT_DONT_OVERWRITE);

        if (st->codecpar->codec_id == AV_CODEC_ID_FLAC) {
            int err = ogg_build_flac_headers(st->codecpar, oggstream,
                                             s->flags & AVFMT_FLAG_BITEXACT,
                                             &st->metadata);
            if (err) {
                av_log(s, AV_LOG_ERROR, "Error writing FLAC headers\n");
                return err;
            }
        } else if (st->codecpar->codec_id == AV_CODEC_ID_SPEEX) {
            int err = ogg_build_speex_headers(st->codecpar, oggstream,
                                              s->flags & AVFMT_FLAG_BITEXACT,
                                              &st->metadata);
            if (err) {
                av_log(s, AV_LOG_ERROR, "Error writing Speex headers\n");
                return err;
            }
        } else if (st->codecpar->codec_id == AV_CODEC_ID_OPUS) {
            int err = ogg_build_opus_headers(st->codecpar, oggstream,
                                             s->flags & AVFMT_FLAG_BITEXACT,
                                             &st->metadata, s->chapters, s->nb_chapters);
            if (err) {
                av_log(s, AV_LOG_ERROR, "Error writing Opus headers\n");
                return err;
            }
        } else if (st->codecpar->codec_id == AV_CODEC_ID_VP8) {
            int err = ogg_build_vp8_headers(s, st, oggstream,
                                            s->flags & AVFMT_FLAG_BITEXACT);
            if (err) {
                av_log(s, AV_LOG_ERROR, "Error writing VP8 headers\n");
                return err;
            }
        } else {
            uint8_t *p;
            const char *cstr = st->codecpar->codec_id == AV_CODEC_ID_VORBIS ? "vorbis" : "theora";
            int header_type = st->codecpar->codec_id == AV_CODEC_ID_VORBIS ? 3 : 0x81;
            int framing_bit = oggstream->attach_count > 0 ? 0 : 
                              st->codecpar->codec_id == AV_CODEC_ID_VORBIS ? 1 : 0;

            if (avpriv_split_xiph_headers(st->codecpar->extradata, st->codecpar->extradata_size,
                                      st->codecpar->codec_id == AV_CODEC_ID_VORBIS ? 30 : 42,
                                      (const uint8_t**)oggstream->header, oggstream->header_len) < 0) {
                av_log(s, AV_LOG_ERROR, "Extradata corrupted\n");
                oggstream->header[1] = NULL;
                return AVERROR_INVALIDDATA;
            }

            p = ogg_write_vorbiscomment(7, s->flags & AVFMT_FLAG_BITEXACT,
                                        &oggstream->header_len[1], &st->metadata,
                                        framing_bit, NULL, 0, oggstream->attach_count);
            oggstream->header[1] = p;
            if (!p)
                return AVERROR(ENOMEM);

            bytestream_put_byte(&p, header_type);
            bytestream_put_buffer(&p, cstr, 6);

            if (st->codecpar->codec_id == AV_CODEC_ID_THEORA) {
                int den = AV_RB32(oggstream->header[0] + 22), num = AV_RB32(oggstream->header[0] + 26);
                /* Make sure to use time base stored in the Theora stream header to write
                   correct timestamps */
                if (st->time_base.num != num || st->time_base.den != den) {
                    av_log(s, AV_LOG_DEBUG, "Changing time base from %d/%d to %d/%d\n",
                           st->time_base.num, st->time_base.den, num, den);
                    avpriv_set_pts_info(st, 64, num, den);
                }
                /** KFGSHIFT is the width of the less significant section of the granule position
                    The less significant section is the frame count since the last keyframe */
                oggstream->kfgshift = ((oggstream->header[0][40]&3)<<3)|(oggstream->header[0][41]>>5);
                oggstream->vrev = oggstream->header[0][9];
                av_log(s, AV_LOG_DEBUG, "theora kfgshift %d, vrev %d\n",
                       oggstream->kfgshift, oggstream->vrev);
            }
        }
    }

    return 0;
}

static int ogg_write_header(AVFormatContext *s)
{
    AVStream *st;
    OGGContext *ogg = s->priv_data;
    OGGStreamContext *oggstream = NULL;
    int j;

    for (j = 0; j < s->nb_streams; j++) {
        if (s->streams[j]->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;
        oggstream = s->streams[j]->priv_data;
        ogg_buffer_data(s, s->streams[j], oggstream->header[0],
                        oggstream->header_len[0], 0, 1);
        oggstream->page.flags |= 2; // bos
        ogg_buffer_page(s, oggstream, NULL);
    }
    ogg_write_pages(s, 2);

    for (j = 0; j < s->nb_streams; j++) {
        if (s->streams[j]->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;
        st = s->streams[j];
        oggstream = st->priv_data;
        if (oggstream->header_len[1]) {
            ogg_buffer_data(s, st, oggstream->header[1],
                            oggstream->header_len[1], 0, 1);
            ogg_buffer_page(s, oggstream, &oggstream->comments);
        }
        if (oggstream->header_len[2]) {
            ogg_buffer_data(s, st, oggstream->header[2],
                            oggstream->header_len[2], 0, 1);
            ogg_buffer_page(s, oggstream, NULL);
        }
    }

    oggstream->page.start_granule = AV_NOPTS_VALUE;

    if (!ogg->attach_count)
        ogg_write_pages(s, 2);

    return 0;
}

static int ogg_write_attached_packet_internal(AVFormatContext *s, AVPacket *pkt)
{
    OGGContext *ogg = s->priv_data;
    AVStream *st = s->streams[pkt->stream_index];
    OGGAttachContext *attachstream = st->priv_data;
    AVStream *base_st = s->streams[attachstream->attach_to];
    OGGStreamContext *oggstream = base_st->priv_data;
    AVIOContext *pb;
    uint8_t *data;
    int data_len;
    int ret;

    attachstream->count++;
    // Only use the first packet received for each attached stream
    if (attachstream->count == 2)
        av_log(s, AV_LOG_WARNING, "Attached stream %d has too many packets, ignoring\n",
               pkt->stream_index);
    if (attachstream->count > 1)
        return 0;

    if (!ogg->attach_count || !oggstream->attach_count) {
        av_log(s, AV_LOG_ERROR, "More attached streams than expected\n");
        return -1;
    }

    avio_open_dyn_buf(&pb);
    if (!pb)
        return AVERROR(ENOMEM);

    if (base_st->codecpar->codec_id == AV_CODEC_ID_FLAC) {
        int picture_len = ff_flac_picture_length(s, pkt);
        if (picture_len >= 1<<24) {
            av_log(s, AV_LOG_ERROR, "Picture block too big %d >= %d\n", picture_len, 1<<24);
            return AVERROR(EINVAL);
        }
        if (oggstream->attach_count == 1)
            avio_w8(pb, 0x86); // last attachment
        else
            avio_w8(pb, 0x06);
        avio_wb24(pb, picture_len);
        ff_flac_write_picture(s, pb, pkt, &oggstream->attached_types);
        data_len = avio_close_dyn_buf(pb, &data);
        if (!data || data_len < 0)
            return AVERROR(ENOMEM);
    } else {
        uint8_t *bin_data;
        int bin_data_len;
        ff_flac_write_picture(s, pb, pkt, &oggstream->attached_types);
        bin_data_len = avio_close_dyn_buf(pb, &bin_data);
        if (!bin_data || bin_data_len < 0)
            return AVERROR(ENOMEM);

        data_len = 4 + 23 + AV_BASE64_SIZE(bin_data_len) - 1;
        data = av_malloc(data_len + 1);
        if (!data)
            return AVERROR(ENOMEM);
        AV_WL32(data, data_len - 4);
        strcpy(data + 4, "METADATA_BLOCK_PICTURE=");
        av_base64_encode(data + 4 + 23, data_len - 4 - 23 + 1, bin_data, bin_data_len);
        av_free(bin_data);

        // add framing bit when required
        if (oggstream->attach_count == 1 &&
            base_st->codecpar->codec_id == AV_CODEC_ID_VORBIS)
            data[data_len++] = 1;
    }

    ret = ogg_append_page(s, &oggstream->comments, data, data_len,
                          base_st->codecpar->codec_id == AV_CODEC_ID_FLAC);
    av_free(data);
    if (ret < 0)
        return ret;

    oggstream->attach_count--;
    ogg->attach_count--;
    if (!ogg->attach_count)
        ogg_write_pages(s, 0);
    return 0;
}

static int ogg_write_packet_internal(AVFormatContext *s, AVPacket *pkt)
{
    OGGContext *ogg = s->priv_data;
    AVStream *st = s->streams[pkt->stream_index];
    OGGStreamContext *oggstream = st->priv_data;
    int ret;
    int64_t granule;

    if (st->codecpar->codec_id == AV_CODEC_ID_THEORA) {
        int64_t pts = oggstream->vrev < 1 ? pkt->pts : pkt->pts + pkt->duration;
        int pframe_count;
        if (pkt->flags & AV_PKT_FLAG_KEY)
            oggstream->last_kf_pts = pts;
        pframe_count = pts - oggstream->last_kf_pts;
        // prevent frame count from overflow if key frame flag is not set
        if (pframe_count >= (1<<oggstream->kfgshift)) {
            oggstream->last_kf_pts += pframe_count;
            pframe_count = 0;
        }
        granule = (oggstream->last_kf_pts<<oggstream->kfgshift) | pframe_count;
    } else if (st->codecpar->codec_id == AV_CODEC_ID_OPUS)
        granule = pkt->pts + pkt->duration +
                  av_rescale_q(st->codecpar->initial_padding,
                               (AVRational){ 1, st->codecpar->sample_rate },
                               st->time_base);
    else if (st->codecpar->codec_id == AV_CODEC_ID_VP8) {
        int64_t pts, invcnt, dist;
        int visible;

        visible = (pkt->data[0] >> 4) & 1;
        pts     = pkt->pts + pkt->duration;
        invcnt  = (oggstream->last_granule >> 30) & 3;
        invcnt  = visible ? 3 : (invcnt == 3 ? 0 : invcnt + 1);
        dist    = (pkt->flags & AV_PKT_FLAG_KEY) ? 0 : ((oggstream->last_granule >> 3) & 0x07ffffff) + 1;

        granule = (pts << 32) | (invcnt << 30) | (dist << 3);
    } else
        granule = pkt->pts + pkt->duration;

    if (oggstream->page.start_granule == AV_NOPTS_VALUE)
        oggstream->page.start_granule = pkt->pts;

    ret = ogg_buffer_data(s, st, pkt->data, pkt->size, granule, 0);
    if (ret < 0)
        return ret;

    if (!ogg->attach_count) {
        ogg_write_pages(s, 0);
    }

    oggstream->last_granule = granule;

    return 0;
}

static int ogg_write_packet(AVFormatContext *s, AVPacket *pkt)
{
    OGGContext *ogg = s->priv_data;
    OGGStreamContext *oggstream;
    int i;

    if (pkt) {
        AVStream *st = s->streams[pkt->stream_index];
        if (st->disposition & AV_DISPOSITION_ATTACHED_PIC)
            return ogg_write_attached_packet_internal(s, pkt);
        else
            return ogg_write_packet_internal(s, pkt);
    }

    if (ogg->attach_count)
        return 0;

    for (i = 0; i < s->nb_streams; i++) {
        if (s->streams[i]->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;
        oggstream = s->streams[i]->priv_data;
        if (oggstream->page.segments_count)
            ogg_buffer_page(s, oggstream, NULL);
    }

    ogg_write_pages(s, 2);
    return 1;
}

static int ogg_write_trailer(AVFormatContext *s)
{
    OGGContext *ogg = s->priv_data;
    OGGStreamContext *oggstream;
    int i;

    if (ogg->attach_count)
        av_log(s, AV_LOG_WARNING, "Some attached images were never written\n");

    /* flush current page if needed */
    for (i = 0; i < s->nb_streams; i++) {
        if (s->streams[i]->disposition & AV_DISPOSITION_ATTACHED_PIC)
            continue;
        oggstream = s->streams[i]->priv_data;

        if (oggstream->page.size > 0)
            ogg_buffer_page(s, oggstream, NULL);
    }

    ogg_write_pages(s, 1);

    return 0;
}

static void ogg_free(AVFormatContext *s)
{
    OGGContext *ogg = s->priv_data;
    OGGPageList *p = ogg->page_list;
    int i;

    for (i = 0; i < s->nb_streams; i++) {
        AVStream *st = s->streams[i];
        if (!(s->streams[i]->disposition & AV_DISPOSITION_ATTACHED_PIC)) {
            OGGStreamContext *oggstream = st->priv_data;
            if (!oggstream)
                continue;
            if (st->codecpar->codec_id == AV_CODEC_ID_FLAC ||
                st->codecpar->codec_id == AV_CODEC_ID_SPEEX ||
                st->codecpar->codec_id == AV_CODEC_ID_OPUS ||
                st->codecpar->codec_id == AV_CODEC_ID_VP8) {
                av_freep(&oggstream->header[0]);
            }
            av_freep(&oggstream->header[1]);
         }
    }

    while (p) {
        OGGPageList *next = p->next;
        av_free(p);
        p = next;
    }
    ogg->page_list = NULL;
}

static int ogg_query_codec(enum AVCodecID id, int std_compliance)
{
    switch (id) {
        case AV_CODEC_ID_VORBIS:
        case AV_CODEC_ID_THEORA:
        case AV_CODEC_ID_SPEEX:
        case AV_CODEC_ID_FLAC:
        case AV_CODEC_ID_OPUS:
        case AV_CODEC_ID_VP8:
            return 1;
        case AV_CODEC_ID_GIF:
        case AV_CODEC_ID_MJPEG:
        case AV_CODEC_ID_PNG:
        case AV_CODEC_ID_TIFF:
        case AV_CODEC_ID_BMP:
            return MKTAG('A', 'P', 'I', 'C');
        default:
            return 0;
    }
    return 0;
}

#if CONFIG_OGG_MUXER
OGG_CLASS(ogg, Ogg)
AVOutputFormat ff_ogg_muxer = {
    .name              = "ogg",
    .long_name         = NULL_IF_CONFIG_SMALL("Ogg"),
    .mime_type         = "application/ogg",
    .extensions        = "ogg"
#if !CONFIG_OGV_MUXER
                         ",ogv"
#endif
#if !CONFIG_SPX_MUXER
                         ",spx"
#endif
#if !CONFIG_OPUS_MUXER
                         ",opus"
#endif
                         ,
    .priv_data_size    = sizeof(OGGContext),
    .audio_codec       = CONFIG_LIBVORBIS_ENCODER ?
                         AV_CODEC_ID_VORBIS : AV_CODEC_ID_FLAC,
    .video_codec       = AV_CODEC_ID_THEORA,
    .init              = ogg_init,
    .write_header      = ogg_write_header,
    .write_packet      = ogg_write_packet,
    .write_trailer     = ogg_write_trailer,
    .deinit            = ogg_free,
    .flags             = AVFMT_TS_NEGATIVE | AVFMT_TS_NONSTRICT | AVFMT_ALLOW_FLUSH,
    .priv_class        = &ogg_muxer_class,
    .query_codec       = ogg_query_codec,
};
#endif

#if CONFIG_OGA_MUXER
OGG_CLASS(oga, Ogg audio)
AVOutputFormat ff_oga_muxer = {
    .name              = "oga",
    .long_name         = NULL_IF_CONFIG_SMALL("Ogg Audio"),
    .mime_type         = "audio/ogg",
    .extensions        = "oga",
    .priv_data_size    = sizeof(OGGContext),
    .audio_codec       = AV_CODEC_ID_FLAC,
    .video_codec       = AV_CODEC_ID_MJPEG,
    .init              = ogg_init,
    .write_header      = ogg_write_header,
    .write_packet      = ogg_write_packet,
    .write_trailer     = ogg_write_trailer,
    .deinit            = ogg_free,
    .flags             = AVFMT_TS_NEGATIVE | AVFMT_ALLOW_FLUSH,
    .priv_class        = &oga_muxer_class,
    .query_codec       = ogg_query_codec,
};
#endif

#if CONFIG_OGV_MUXER
OGG_CLASS(ogv, Ogg video)
AVOutputFormat ff_ogv_muxer = {
    .name              = "ogv",
    .long_name         = NULL_IF_CONFIG_SMALL("Ogg Video"),
    .mime_type         = "video/ogg",
    .extensions        = "ogv",
    .priv_data_size    = sizeof(OGGContext),
    .audio_codec       = CONFIG_LIBVORBIS_ENCODER ?
                         AV_CODEC_ID_VORBIS : AV_CODEC_ID_FLAC,
    .video_codec       = CONFIG_LIBTHEORA_ENCODER ?
                         AV_CODEC_ID_THEORA : AV_CODEC_ID_VP8,
    .init              = ogg_init,
    .write_header      = ogg_write_header,
    .write_packet      = ogg_write_packet,
    .write_trailer     = ogg_write_trailer,
    .deinit            = ogg_free,
    .flags             = AVFMT_TS_NEGATIVE | AVFMT_TS_NONSTRICT | AVFMT_ALLOW_FLUSH,
    .priv_class        = &ogv_muxer_class,
    .query_codec       = ogg_query_codec,
};
#endif

#if CONFIG_SPX_MUXER
OGG_CLASS(spx, Ogg Speex)
AVOutputFormat ff_spx_muxer = {
    .name              = "spx",
    .long_name         = NULL_IF_CONFIG_SMALL("Ogg Speex"),
    .mime_type         = "audio/ogg",
    .extensions        = "spx",
    .priv_data_size    = sizeof(OGGContext),
    .audio_codec       = AV_CODEC_ID_SPEEX,
    .video_codec       = AV_CODEC_ID_MJPEG,
    .init              = ogg_init,
    .write_header      = ogg_write_header,
    .write_packet      = ogg_write_packet,
    .write_trailer     = ogg_write_trailer,
    .deinit            = ogg_free,
    .flags             = AVFMT_TS_NEGATIVE | AVFMT_ALLOW_FLUSH,
    .priv_class        = &spx_muxer_class,
    .query_codec       = ogg_query_codec,
};
#endif

#if CONFIG_OPUS_MUXER
OGG_CLASS(opus, Ogg Opus)
AVOutputFormat ff_opus_muxer = {
    .name              = "opus",
    .long_name         = NULL_IF_CONFIG_SMALL("Ogg Opus"),
    .mime_type         = "audio/ogg",
    .extensions        = "opus",
    .priv_data_size    = sizeof(OGGContext),
    .audio_codec       = AV_CODEC_ID_OPUS,
    .video_codec       = AV_CODEC_ID_MJPEG,
    .init              = ogg_init,
    .write_header      = ogg_write_header,
    .write_packet      = ogg_write_packet,
    .write_trailer     = ogg_write_trailer,
    .deinit            = ogg_free,
    .flags             = AVFMT_TS_NEGATIVE | AVFMT_ALLOW_FLUSH,
    .priv_class        = &opus_muxer_class,
    .query_codec       = ogg_query_codec,
};
#endif
