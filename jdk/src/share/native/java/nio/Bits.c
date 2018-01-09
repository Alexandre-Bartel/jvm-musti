/*
 * Copyright (c) 2002, 2010, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

/*
 */

#include "jni.h"
#include "jni_util.h"
#include "jlong.h"
#include <string.h>

/*
 * WARNING:
 *
 * Do not replace instances of:
 *
 *   if (length > MBYTE)
 *     size = MBYTE;
 *   else
 *     size = length;
 *
 * with
 *
 *   size = (length > MBYTE ? MBYTE : length);
 *
 * This expression causes a c compiler assertion failure when compiling on
 * 32-bit sparc.
 */

#define MBYTE 1048576

#define GETCRITICAL_OR_RETURN(bytes, env, obj) { \
    bytes = (*env)->GetPrimitiveArrayCritical(env, obj, NULL); \
    if (bytes == NULL)  { \
        if ((*env)->ExceptionOccurred(env) == NULL) \
            JNU_ThrowInternalError(env, "Unable to get array"); \
        return; \
    } \
}

#define RELEASECRITICAL(bytes, env, obj, mode) { \
    (*env)->ReleasePrimitiveArrayCritical(env, obj, bytes, mode); \
}

#define SWAPSHORT(x) ((jshort)(((x) << 8) | (((x) >> 8) & 0xff)))
#define SWAPINT(x)   ((jint)((SWAPSHORT((jshort)(x)) << 16) | \
                            (SWAPSHORT((jshort)((x) >> 16)) & 0xffff)))
#define SWAPLONG(x)  ((jlong)(((jlong)SWAPINT((jint)(x)) << 32) | \
                              ((jlong)SWAPINT((jint)((x) >> 32)) & 0xffffffff)))

/* The destination buffer passed to Java_java_nio_Bits_copyFromShor<type>tArray
 * function and the source buffer passed to Java_java_nio_Bits_copyTo<type>Array
 * may not be aligned on <type>'s boundary. Inform the compiler about this via
 * 'unaligned' attribute, provided it supports this attribute. For recent 
 * compilers, use __has_attribute preprocessor predicate; if it is not available,
 * we know that GCC supports it.
 */
#ifndef __has_attribute
#define __has_attribute(x) 0
#endif

#if defined(__GNUC__) || __has_attribute(aligned)
typedef jshort __attribute__((aligned(1))) jshort_unaligned;
typedef jint __attribute__((aligned(1))) jint_unaligned;
typedef jlong __attribute__((aligned(1))) jlong_unaligned;
#else
typedef jshort jshort_unaligned;
typedef jint jint_unaligned;
typedef jlong jlong_unaligned;
#endif

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyFromShortArray(JNIEnv *env, jobject this, jobject src,
                                      jlong srcPos, jlong dstAddr, jlong length)
{
    jbyte *bytes;
    size_t size;
    jshort *srcShort, *endShort;
    jshort_unaligned *dstShort;
    jshort tmpShort;

    dstShort = (jshort_unaligned *)jlong_to_ptr(dstAddr);

    while (length > 0) {
        /* do not change this if-else statement, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, src);

        srcShort = (jshort *)(bytes + srcPos);
        endShort = srcShort + (size / sizeof(jshort));
        while (srcShort < endShort) {
          tmpShort = *srcShort++;
          *dstShort++ = SWAPSHORT(tmpShort);
        }

        RELEASECRITICAL(bytes, env, src, JNI_ABORT);

        length -= size;
        dstAddr += size;
        srcPos += size;
    }
}

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyToShortArray(JNIEnv *env, jobject this, jlong srcAddr,
                                    jobject dst, jlong dstPos, jlong length)
{
    jbyte *bytes;
    size_t size;
    jshort_unaligned *srcShort, *endShort;
    jshort *dstShort;
    jshort tmpShort;

    srcShort = (jshort_unaligned *)jlong_to_ptr(srcAddr);

    while (length > 0) {
        /* do not change this if-else statement, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, dst);

        dstShort = (jshort *)(bytes + dstPos);
        endShort = srcShort + (size / sizeof(jshort));
        while (srcShort < endShort) {
            tmpShort = *srcShort++;
            *dstShort++ = SWAPSHORT(tmpShort);
        }

        RELEASECRITICAL(bytes, env, dst, 0);

        length -= size;
        srcAddr += size;
        dstPos += size;
    }
}

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyFromIntArray(JNIEnv *env, jobject this, jobject src,
                                    jlong srcPos, jlong dstAddr, jlong length)
{
    jbyte *bytes;
    size_t size;
    jint *srcInt, *endInt;
    jint_unaligned *dstInt;
    jint tmpInt;

    dstInt = (jint_unaligned *)jlong_to_ptr(dstAddr);

    while (length > 0) {
        /* do not change this code, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, src);

        srcInt = (jint *)(bytes + srcPos);
        endInt = srcInt + (size / sizeof(jint));
        while (srcInt < endInt) {
            tmpInt = *srcInt++;
            *dstInt++ = SWAPINT(tmpInt);
        }

        RELEASECRITICAL(bytes, env, src, JNI_ABORT);

        length -= size;
        dstAddr += size;
        srcPos += size;
    }
}

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyToIntArray(JNIEnv *env, jobject this, jlong srcAddr,
                                  jobject dst, jlong dstPos, jlong length)
{
    jbyte *bytes;
    size_t size;
    jint_unaligned *srcInt, *endInt;
    jint *dstInt;
    jint tmpInt;

    srcInt = (jint_unaligned *)jlong_to_ptr(srcAddr);

    while (length > 0) {
        /* do not change this code, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, dst);

        dstInt = (jint *)(bytes + dstPos);
        endInt = srcInt + (size / sizeof(jint));
        while (srcInt < endInt) {
            tmpInt = *srcInt++;
            *dstInt++ = SWAPINT(tmpInt);
        }

        RELEASECRITICAL(bytes, env, dst, 0);

        length -= size;
        srcAddr += size;
        dstPos += size;
    }
}

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyFromLongArray(JNIEnv *env, jobject this, jobject src,
                                     jlong srcPos, jlong dstAddr, jlong length)
{
    jbyte *bytes;
    size_t size;
    jlong *srcLong, *endLong;
    jlong_unaligned *dstLong;
    jlong tmpLong;

    dstLong = (jlong_unaligned *)jlong_to_ptr(dstAddr);

    while (length > 0) {
        /* do not change this code, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, src);

        srcLong = (jlong *)(bytes + srcPos);
        endLong = srcLong + (size / sizeof(jlong));
        while (srcLong < endLong) {
            tmpLong = *srcLong++;
            *dstLong++ = SWAPLONG(tmpLong);
        }

        RELEASECRITICAL(bytes, env, src, JNI_ABORT);

        length -= size;
        dstAddr += size;
        srcPos += size;
    }
}

JNIEXPORT void JNICALL
Java_java_nio_Bits_copyToLongArray(JNIEnv *env, jobject this, jlong srcAddr,
                                   jobject dst, jlong dstPos, jlong length)
{
    jbyte *bytes;
    size_t size;
    jlong_unaligned *srcLong, *endLong;
    jlong *dstLong;
    jlong tmpLong;

    srcLong = (jlong_unaligned *)jlong_to_ptr(srcAddr);

    while (length > 0) {
        /* do not change this code, see WARNING above */
        if (length > MBYTE)
            size = MBYTE;
        else
            size = (size_t)length;

        GETCRITICAL_OR_RETURN(bytes, env, dst);

        dstLong = (jlong *)(bytes + dstPos);
        endLong = srcLong + (size / sizeof(jlong));
        while (srcLong < endLong) {
            tmpLong = *srcLong++;
            *dstLong++ = SWAPLONG(tmpLong);
        }

        RELEASECRITICAL(bytes, env, dst, 0);

        length -= size;
        srcAddr += size;
        dstPos += size;
    }
}
