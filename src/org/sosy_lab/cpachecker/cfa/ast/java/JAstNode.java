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
package org.sosy_lab.cpachecker.cfa.ast.java;

import org.sosy_lab.cpachecker.cfa.ast.AAstNode;
import org.sosy_lab.cpachecker.cfa.ast.c.CAstNodeVisitor;

/**
 * Interface for all AST Nodes of the Java AST.
 * All classes representing Java AST Nodes have to implement this interface.
 */
public interface JAstNode extends AAstNode {

  <R, X extends Exception> R accept(JAstNodeVisitor<R, X> v) throws X;

  @Deprecated // Call accept() directly
  @Override
  default <
          R,
          R1 extends R,
          R2 extends R,
          X1 extends Exception,
          X2 extends Exception,
          V extends CAstNodeVisitor<R1, X1> & JAstNodeVisitor<R2, X2>>
      R accept_(V pV) throws X1, X2 {
    return accept((JAstNodeVisitor<R2, X2>) pV);
  }
}
