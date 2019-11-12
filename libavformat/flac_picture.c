/*
 * Raw FLAC picture parser
 * Copyright (c) 2001 Fabrice Bellard
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

#include "libavutil/intreadwrite.h"
#include "libavcodec/bytestream.h"
#include "libavutil/pixdesc.h"
#include "libavcodec/png.h"
#include "avformat.h"
#include "flac_picture.h"
#include "id3v2.h"
#include "internal.h"

int ff_flac_parse_picture(AVFormatContext *s, uint8_t *buf, int buf_size, int ogg_index)
{
    const CodecMime *mime = ff_id3v2_mime_tags;
    enum AVCodecID id = AV_CODEC_ID_NONE;
    AVBufferRef *data = NULL;
    uint8_t mimetype[64], *desc = NULL;
    GetByteContext g;
    AVStream *st;
    int width, height, ret = 0;
    unsigned int len, type;

    if (buf_size < 34) {
        av_log(s, AV_LOG_ERROR, "Attached picture metadata block too short\n");
        if (s->error_recognition & AV_EF_EXPLODE)
            return AVERROR_INVALIDDATA;
        return 0;
    }

    bytestream2_init(&g, buf, buf_size);

    /* read the picture type */
    type = bytestream2_get_be32u(&g);
    if (type >= FF_ARRAY_ELEMS(ff_id3v2_picture_types)) {
        av_log(s, AV_LOG_ERROR, "Invalid picture type: %d.\n", type);
        if (s->error_recognition & AV_EF_EXPLODE) {
            return AVERROR_INVALIDDATA;
        }
        type = 0;
    }

    /* picture mimetype */
    len = bytestream2_get_be32u(&g);
    if (len <= 0 || len >= sizeof(mimetype)) {
        av_log(s, AV_LOG_ERROR, "Could not read mimetype from an attached "
               "picture.\n");
        if (s->error_recognition & AV_EF_EXPLODE)
            return AVERROR_INVALIDDATA;
        return 0;
    }
    if (len + 24 > bytestream2_get_bytes_left(&g)) {
        av_log(s, AV_LOG_ERROR, "Attached picture metadata block too short\n");
        if (s->error_recognition & AV_EF_EXPLODE)
            return AVERROR_INVALIDDATA;
        return 0;
    }
    bytestream2_get_bufferu(&g, mimetype, len);
    mimetype[len] = 0;

    while (mime->id != AV_CODEC_ID_NONE) {
        if (!strncmp(mime->str, mimetype, sizeof(mimetype))) {
            id = mime->id;
            break;
        }
        mime++;
    }
    if (id == AV_CODEC_ID_NONE) {
        av_log(s, AV_LOG_ERROR, "Unknown attached picture mimetype: %s.\n",
               mimetype);
        if (s->error_recognition & AV_EF_EXPLODE)
            return AVERROR_INVALIDDATA;
        return 0;
    }

    /* picture description */
    len = bytestream2_get_be32u(&g);
    if (len > bytestream2_get_bytes_left(&g) - 20) {
        av_log(s, AV_LOG_ERROR, "Attached picture metadata block too short\n");
        if (s->error_recognition & AV_EF_EXPLODE)
            return AVERROR_INVALIDDATA;
        return 0;
    }
    if (len > 0) {
        if (!(desc = av_malloc(len + 1))) {
            return AVERROR(ENOMEM);
        }

        bytestream2_get_bufferu(&g, desc, len);
        desc[len] = 0;
    }

    /* picture metadata */
    width  = bytestream2_get_be32u(&g);
    height = bytestream2_get_be32u(&g);
    bytestream2_skipu(&g, 8);

    /* picture data */
    len = bytestream2_get_be32u(&g);
    if (len <= 0 || len > bytestream2_get_bytes_left(&g)) {
        av_log(s, AV_LOG_ERROR, "Attached picture metadata block too short\n");
        if (s->error_recognition & AV_EF_EXPLODE)
            ret = AVERROR_INVALIDDATA;
        goto fail;
    }
    if (!(data = av_buffer_alloc(len + AV_INPUT_BUFFER_PADDING_SIZE))) {
        RETURN_ERROR(AVERROR(ENOMEM));
    }
    bytestream2_get_bufferu(&g, data->data, len);
    memset(data->data + len, 0, AV_INPUT_BUFFER_PADDING_SIZE);

    if (AV_RB64(data->data) == PNGSIG)
        id = AV_CODEC_ID_PNG;

    st = avformat_new_stream(s, NULL);
    if (!st) {
        RETURN_ERROR(AVERROR(ENOMEM));
    }

    av_init_packet(&st->attached_pic);
    st->attached_pic.buf          = data;
    st->attached_pic.data         = data->data;
    st->attached_pic.size         = len;
    st->attached_pic.stream_index = st->index;
    st->attached_pic.flags       |= AV_PKT_FLAG_KEY;

    st->disposition      |= AV_DISPOSITION_ATTACHED_PIC;
    st->codecpar->codec_type = AVMEDIA_TYPE_VIDEO;
    st->codecpar->codec_id   = id;
    st->codecpar->width      = width;
    st->codecpar->height     = height;
    av_dict_set(&st->metadata, "comment", ff_id3v2_picture_types[type], 0);
    if (desc)
        av_dict_set(&st->metadata, "title", desc, AV_DICT_DONT_STRDUP_VAL);
    if (ogg_index >= 0)
        av_dict_set_int(&st->metadata, "ogg_attached", ogg_index, 0);

    return 0;

fail:
    av_buffer_unref(&data);
    av_freep(&desc);

    return ret;
}

int ff_flac_picture_length(struct AVFormatContext *s, AVPacket *pkt) {
    const CodecMime *mime = ff_id3v2_mime_tags;
    AVDictionaryEntry *e;
    const char *mimetype = NULL, *desc = "";
    const AVStream *st = s->streams[pkt->stream_index];
    int mimelen, desclen;

    if (!pkt->data)
        return 0;

    /* get the mimetype */
    while (mime->id != AV_CODEC_ID_NONE) {
        if (mime->id == st->codecpar->codec_id) {
            mimetype = mime->str;
            break;
        }
        mime++;
    }
    if (!mimetype)
        return 0;
    mimelen = strlen(mimetype);

    /* get the description */
    if ((e = av_dict_get(st->metadata, "title", NULL, 0)))
        desc = e->value;
    desclen = strlen(desc);

    return 4 + 4 + mimelen + 4 + desclen + 4 + 4 + 4 + 4 + 4 + pkt->size;
}

int ff_flac_write_picture(struct AVFormatContext *s, AVIOContext *pb,
                          AVPacket *pkt, unsigned *attached_types)
{
    const AVPixFmtDescriptor *pixdesc;
    const CodecMime *mime = ff_id3v2_mime_tags;
    AVDictionaryEntry *e;
    const char *mimetype = NULL, *desc = "";
    const AVStream *st = s->streams[pkt->stream_index];
    int i, mimelen, desclen, type = 0;

    if (!pkt->data)
        return 0;

    while (mime->id != AV_CODEC_ID_NONE) {
        if (mime->id == st->codecpar->codec_id) {
            mimetype = mime->str;
            break;
        }
        mime++;
    }
    if (!mimetype) {
        av_log(s, AV_LOG_ERROR, "No mimetype is known for stream %d, cannot "
               "write an attached picture.\n", st->index);
        return AVERROR(EINVAL);
    }
    mimelen = strlen(mimetype);

    /* get the picture type */
    e = av_dict_get(st->metadata, "comment", NULL, 0);
    for (i = 0; e && i < FF_ARRAY_ELEMS(ff_id3v2_picture_types); i++) {
        if (!av_strcasecmp(e->value, ff_id3v2_picture_types[i])) {
            type = i;
            break;
        }
    }

    if ((*attached_types & (1 << type)) & 0x6) {
        av_log(s, AV_LOG_ERROR, "Duplicate attachment for type '%s'\n", ff_id3v2_picture_types[type]);
        return AVERROR(EINVAL);
    }

    if (type == 1 && (st->codecpar->codec_id != AV_CODEC_ID_PNG ||
                      st->codecpar->width != 32 ||
                      st->codecpar->height != 32)) {
        av_log(s, AV_LOG_ERROR, "File icon attachment must be a 32x32 PNG");
        return AVERROR(EINVAL);
    }

    *attached_types |= (1 << type);

    /* get the description */
    if ((e = av_dict_get(st->metadata, "title", NULL, 0)))
        desc = e->value;
    desclen = strlen(desc);

    avio_wb32(pb, type);

    avio_wb32(pb, mimelen);
    avio_write(pb, mimetype, mimelen);

    avio_wb32(pb, desclen);
    avio_write(pb, desc, desclen);

    avio_wb32(pb, st->codecpar->width);
    avio_wb32(pb, st->codecpar->height);
    if ((pixdesc = av_pix_fmt_desc_get(st->codecpar->format)))
        avio_wb32(pb, av_get_bits_per_pixel(pixdesc));
    else
        avio_wb32(pb, 0);
    avio_wb32(pb, 0);

    avio_wb32(pb, pkt->size);
    avio_write(pb, pkt->data, pkt->size);
    return 0;
}
