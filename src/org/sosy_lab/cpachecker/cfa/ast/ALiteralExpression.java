/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.sosy_lab.cpachecker.cfa.ast;

import java.util.List;
import org.sosy_lab.cpachecker.cfa.types.Type;


public abstract class ALiteralExpression extends AbstractExpression {

  public ALiteralExpression(FileLocation pFileLocation, Type pType) {
    super(pFileLocation, pType);
  }

  public abstract Object getValue();


  @Override
  public String toParenthesizedASTString() {
    // literal expression never need parentheses
    return toASTString();
  }

  @Override
  public int hashCode() {
    int prime = 31;
    int result = 7;
    return prime * result + super.hashCode();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }

    if (!(obj instanceof ALiteralExpression)) {
      return false;
    }

    return super.equals(obj);
  }
  @Override
  public boolean equalVar(String pVar) {
    // TODO Auto-generated method stub
    if(pVar.equals("")) {
      return true;
    } else {
      return false;
    }
  }

  @Override
  public String extractJudgeVar() {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public void getAllLVars(List<String> l){
    l.add(getValue().toString()+"+");
  }
}