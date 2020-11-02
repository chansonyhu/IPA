/*
 * CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.cpachecker.cfa.ast.c;

import org.sosy_lab.cpachecker.cfa.ast.AbstractSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.types.c.CType;

public class CDummyDeclaration implements CSimpleDeclaration {

  private final String name;

  public CDummyDeclaration() {
    name = "__DUMMY__";
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public String getOrigName() {
    return name;
  }

  @Override
  public CType getType() {
    return null;
  }

  @Override
  public String getQualifiedName() {
    return name;
  }

  @Override
  public <R, X extends Exception> R accept(CSimpleDeclarationVisitor<R, X> v) throws X {
    return null;
  }

  @Override
  public <R, X extends Exception> R accept(CAstNodeVisitor<R, X> v) throws X {
    return null;
  }

  @Override
  public FileLocation getFileLocation() {
    return null;
  }

  @Override
  public String toASTString() {
    return null;
  }

  @Override
  public String toParenthesizedASTString() {
    return null;
  }
}
