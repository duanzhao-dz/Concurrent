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
import java.util.Objects;
import org.ictt.GlobalInfo.MarkLoop;
import org.sosy_lab.cpachecker.cfa.types.Type;


/**
 * This is the abstract Class for all Expressions with two Operands and one Operator.
 */
public abstract class ABinaryExpression extends AbstractExpression {


  private final AExpression operand1;
  private final AExpression operand2;
  private final ABinaryOperator operator;

  public ABinaryExpression(FileLocation pFileLocation, Type pType,
      final AExpression pOperand1,
      final AExpression pOperand2,
      final ABinaryOperator pOperator) {
    super(pFileLocation, pType);
    operand1 = pOperand1;
    operand2 = pOperand2;
    operator = pOperator;
  }



  public AExpression getOperand1() {
    return operand1;
  }

  public AExpression getOperand2() {
    return operand2;
  }

  public ABinaryOperator getOperator() {
    return operator;
  }

  @Override
  public String toASTString() {
    return operand1.toParenthesizedASTString() + " "
        + operator.getOperator() + " " + operand2.toParenthesizedASTString();
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 7;
    result = prime * result + Objects.hashCode(operand1);
    result = prime * result + Objects.hashCode(operand2);
    result = prime * result + Objects.hashCode(operator);
    result = prime * result + super.hashCode();
    return result;
  }



  /* (non-Javadoc)
   * @see java.lang.Object#equals(java.lang.Object)
   */
  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }

    if (!(obj instanceof ABinaryExpression)
        || !super.equals(obj)) {
      return false;
    }

    ABinaryExpression other = (ABinaryExpression) obj;

    return Objects.equals(other.operand1, operand1)
            && Objects.equals(other.operand2, operand2)
            && Objects.equals(other.operator, operator);
  }

  @Override
  public String toString() {
    return "operand1=[" + getOperand1() +
        "], operand2=[" + getOperand2() +
        "], operator=[" + getOperator() + "]";
  }

  public static  interface ABinaryOperator {
    /**
     * Returns the string representation of this operator (e.g. "*", "+").
     */
    public String getOperator();
  }
  @Override
  public void getAllLVars(List<String> l){
    operand1.getAllVars(l);
  }
  @Override
  public void getAllRVars(List<String> l){
    operand2.getAllVars(l);
  }
  @Override
  public void getAllVars(List<String> l){
    operand1.getAllVars(l);
    operand2.getAllVars(l);
  }
  @Override
  public boolean equalVar(String pVar) {
    // TODO Auto-generated method stub
    String op=operator.getOperator();
    if(op.equals("+")||op.equals("-")){
      boolean bool=(operand1.equalVar(pVar)&&operand2.equalVar(""))||
          (operand2.equalVar(pVar)&&operand1.equalVar(""));
      if(bool){
        if(operand1 instanceof ALiteralExpression){
          String s=String.valueOf(((ALiteralExpression) operand1).getValue());
          s=op.equals("+")?s:"-"+s;
          MarkLoop.addValue.add(s);
        }
        else if(operand2 instanceof ALiteralExpression){
          String s=String.valueOf(((ALiteralExpression) operand2).getValue());
          s=op.equals("+")?s:"-"+s;
          MarkLoop.addValue.add(s);
        }
      }
       return bool;
    }
    return false;
  }

  @Override
  public String extractJudgeVar() {
    // TODO Auto-generated method stub
    return operand1.extractJudgeVar();
  }
}
