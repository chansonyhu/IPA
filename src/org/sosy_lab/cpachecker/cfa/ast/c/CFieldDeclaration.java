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
package org.sosy_lab.cpachecker.cfa.ast.c;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Map;
import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.ast.AbstractExpression;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.types.c.CComplexType.ComplexTypeKind;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;

public class CFieldDeclaration implements CSimpleDeclaration {

  // port->serial->disc_mutex
  // struct mutex, struct usb_serial, struct usb_serial_port
  private final CSimpleDeclaration declaration; // original owner
  private final String value;

  public CFieldDeclaration(CSimpleDeclaration pDecl, String pVal) {
    declaration = pDecl;
    value = pVal;
  }

  public CSimpleDeclaration getDeclaration() {
    return declaration;
  }

//  public CFieldDeclaration0(CFieldReference ref) {
//    value = ref.toString();
//    AbstractExpression tmp = ref;
//    while (!tmp.getClass().getSimpleName().equals("CIdExpression")) {
//      if(tmp instanceof CFieldReference) {
//        tmp = (AbstractExpression) ((CFieldReference) tmp).getFieldOwner();
//      } else {
//        throw new UnsupportedOperationException();
//      }
//    }
//    checkArgument(tmp instanceof CIdExpression);
//    declaration = ((CIdExpression) tmp).getDeclaration();
//  }

  @Override
  public String getName() {
    return value;
  }

  @Override
  public String getOrigName() {
    return value;
  }

  @Override
  public CType getType() {
    return null;
  }

  @Override
  public String getQualifiedName() {
    return value;
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
    return value;
  }

  @Override
  public String toParenthesizedASTString() {
    return value;
  }

  @Override
  public boolean equals(Object obj) {
    if(!ImpactedHelper.getInstance().readyForAnalysis) {
      CFieldDeclaration objDeclaration = ((CFieldDeclaration)obj);
      return declaration.getQualifiedName().equals(objDeclaration.getDeclaration().getQualifiedName()) &&
          value.equals(((CFieldDeclaration) obj).getQualifiedName());
    }
    return super.equals(obj);
  }
}
