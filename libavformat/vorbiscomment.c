/*
 * VorbisComment writer
 * Copyright (c) 2009 James Darnley
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

#include "avformat.h"
#include "flac_picture.h"
#include "metadata.h"
#include "vorbiscomment.h"
#include "libavcodec/bytestream.h"
#include "libavutil/base64.h"
#include "libavutil/dict.h"

/**
 * VorbisComment metadata conversion mapping.
 * from Ogg Vorbis I format specification: comment field and header specification
 * http://xiph.org/vorbis/doc/v-comment.html
 */
const AVMetadataConv ff_vorbiscomment_metadata_conv[] = {
    { "ALBUMARTIST", "album_artist"},
    { "TRACKNUMBER", "track"  },
    { "DISCNUMBER",  "disc"   },
    { "DESCRIPTION", "comment" },
    { 0 }
};

int64_t ff_vorbiscomment_length(AVDictionary *m, const char *vendor_string,
                                AVChapter **chapters, unsigned int nb_chapters)
{
    int64_t len = 8;
    len += strlen(vendor_string);
    if (m) {
        AVDictionaryEntry *tag = NULL;
        while ((tag = av_dict_get(m, "", tag, AV_DICT_IGNORE_SUFFIX))) {
            len += 4 +strlen(tag->key) + 1 + strlen(tag->value);
        }
    }
    if (chapters && nb_chapters) {
        for (int i = 0; i < nb_chapters; i++) {
            AVDictionaryEntry *tag = NULL;
            len += 4 + 12 + 1 + 10;
            while ((tag = av_dict_get(chapters[i]->metadata, "", tag, AV_DICT_IGNORE_SUFFIX))) {
                int64_t len1 = !strcmp(tag->key, "title") ? 4 : strlen(tag->key);
                len += 4 + 10 + len1 + 1 + strlen(tag->value);
            }
        }
    }
    return len;
}

int ff_vorbiscomment_write(uint8_t **p, AVDictionary **m, const char *vendor_string,
                           AVChapter **chapters, unsigned int nb_chapters,
                           int external_count)
{
    int cm_count = 0;
    bytestream_put_le32(p, strlen(vendor_string));
    bytestream_put_buffer(p, vendor_string, strlen(vendor_string));
    if (chapters && nb_chapters) {
        for (int i = 0; i < nb_chapters; i++) {
            cm_count += av_dict_count(chapters[i]->metadata) + 1;
        }
    }
    int count = av_dict_count(*m) + cm_count + external_count;
    bytestream_put_le32(p, count);

    if (*m) {
        AVDictionaryEntry *tag = NULL;
        while ((tag = av_dict_get(*m, "", tag, AV_DICT_IGNORE_SUFFIX))) {
            int64_t len1 = strlen(tag->key);
            int64_t len2 = strlen(tag->value);
            if (len1+1+len2 > UINT32_MAX)
                return AVERROR(EINVAL);
            bytestream_put_le32(p, len1+1+len2);
            bytestream_put_buffer(p, tag->key, len1);
            bytestream_put_byte(p, '=');
            bytestream_put_buffer(p, tag->value, len2);
        }
    }
    if (chapters && nb_chapters) {
        for (int i = 0; i < nb_chapters; i++) {
            AVChapter *chp = chapters[i];
            char chapter_time[13];
            char chapter_number[4];
            int h, m, s, ms;

            s  = av_rescale(chp->start, chp->time_base.num, chp->time_base.den);
            h  = s / 3600;
            m  = (s / 60) % 60;
            ms = av_rescale_q(chp->start, chp->time_base, av_make_q(   1, 1000)) % 1000;
            s  = s % 60;
            snprintf(chapter_number, sizeof(chapter_number), "%03d", i);
            snprintf(chapter_time, sizeof(chapter_time), "%02d:%02d:%02d.%03d", h, m, s, ms);
            bytestream_put_le32(p, 10+1+12);
            bytestream_put_buffer(p, "CHAPTER", 7);
            bytestream_put_buffer(p, chapter_number, 3);
            bytestream_put_byte(p, '=');
            bytestream_put_buffer(p, chapter_time, 12);

            AVDictionaryEntry *tag = NULL;
            while ((tag = av_dict_get(chapters[i]->metadata, "", tag, AV_DICT_IGNORE_SUFFIX))) {
                int64_t len1 = !strcmp(tag->key, "title") ? 4 : strlen(tag->key);
                int64_t len2 = strlen(tag->value);
                if (len1+1+len2+10 > UINT32_MAX)
                    return AVERROR(EINVAL);
                bytestream_put_le32(p, 10+len1+1+len2);
                bytestream_put_buffer(p, "CHAPTER", 7);
                bytestream_put_buffer(p, chapter_number, 3);
                if (!strcmp(tag->key, "title"))
                    bytestream_put_buffer(p, "NAME", 4);
                else
                    bytestream_put_buffer(p, tag->key, len1);
                bytestream_put_byte(p, '=');
                bytestream_put_buffer(p, tag->value, len2);
            }
        }
    }
    return 0;
}
