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
package org.sosy_lab.cpachecker.cfa.model.c;

import static com.google.common.base.Preconditions.checkArgument;

import org.sosy_lab.cpachecker.cfa.model.CFANode;

public class CLabelNode extends CFANode {

  private final String label;

  public CLabelNode(String pFunctionName, String pLabel) {
    super(pFunctionName);
    checkArgument(!pLabel.isEmpty());
    label = pLabel;
  }

  public String getLabel() {
    return label;
  }
}
