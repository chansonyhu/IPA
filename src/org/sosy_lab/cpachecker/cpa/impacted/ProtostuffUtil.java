/*
 * CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.impacted;

import edu.umd.cs.findbugs.graph.Graph;
import io.protostuff.GraphIOUtil;
import io.protostuff.LinkedBuffer;
import io.protostuff.ProtostuffIOUtil;
import io.protostuff.Schema;
import io.protostuff.runtime.RuntimeSchema;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class ProtostuffUtil {
  private static Map<Class<?>, Schema<?>> cachedSchema = new ConcurrentHashMap<Class<?>, Schema<?>>();

  private static <T> Schema<T> getSchema(Class<T> clazz) {
    @SuppressWarnings("unchecked")
    Schema<T> schema = (Schema<T>) cachedSchema.get(clazz);
    if (schema == null) {
      schema = RuntimeSchema.getSchema(clazz);
      if (schema != null) {
        cachedSchema.put(clazz, schema);
      }
    }
    return schema;
  }

  /**
   * 将对象序列化
   * @param obj 对象
   * @return
   */
  public static <T> byte[] serializer(T obj) {
    @SuppressWarnings("unchecked")
    Class<T> clazz = (Class<T>) obj.getClass();
    LinkedBuffer buffer = LinkedBuffer.allocate(LinkedBuffer.DEFAULT_BUFFER_SIZE);
    try {
      Schema<T> schema = getSchema(clazz);
      return ProtostuffIOUtil.toByteArray(obj, schema, buffer);
    } catch (Exception e) {
      throw new IllegalStateException(e.getMessage(), e);
    } finally {
      buffer.clear();
    }
  }

  /**
   * 将对象序列化（解决循环引用问题）
   * @param obj 对象
   * @return
   */
  public static <T> byte[] graph_serializer(T obj) {
    @SuppressWarnings("unchecked")
    Class<T> clazz = (Class<T>) obj.getClass();
    LinkedBuffer buffer = LinkedBuffer.allocate(LinkedBuffer.DEFAULT_BUFFER_SIZE * 100);
    try {
      Schema<T> schema = getSchema(clazz);
      return GraphIOUtil.toByteArray(obj, schema, buffer);
    } catch (Exception e) {
      throw new IllegalStateException(e.getMessage(), e);
    } finally {
      buffer.clear();
    }
  }
  /**
   * 将字节数组数据反序列化
   * @param data 字节数组
   * @param clazz 对象
   * @return
   */
  public static <T> T deserializer(byte[] data, Class<T> clazz) {
    try {
      //Attention: clazz need have non-para constructor
      //yqs17: We add this to class PredicatePrecision
      T obj = clazz.newInstance();
      Schema<T> schema = getSchema(clazz);
      ProtostuffIOUtil.mergeFrom(data, obj, schema);
      return obj;
    } catch (InstantiationException e) {
      e.getMessage();
      throw new IllegalStateException(e.getMessage(), e);
    } catch (Exception e) {
      throw new IllegalStateException(e.getMessage(), e);
    }
  }
}
