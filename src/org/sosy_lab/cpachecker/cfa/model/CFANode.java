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
package org.sosy_lab.cpachecker.cfa.model;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class CFANode implements Comparable<CFANode> {

  private static final UniqueIdGenerator idGenerator = new UniqueIdGenerator();

  private final int nodeNumber;

  private final List<CFAEdge> leavingEdges = new ArrayList<>(1);
  private final List<CFAEdge> enteringEdges = new ArrayList<>(1);

  // is start node of a loop?
  private boolean isLoopStart = false;

  // in which function is that node?
  private final String functionName;

  // list of summary edges
  private FunctionSummaryEdge leavingSummaryEdge = null;
  private FunctionSummaryEdge enteringSummaryEdge = null;

  // reverse postorder sort id, smaller if it appears later in sorting
  private int reversePostorderId = 0;

  /********************added code****************/
  private BooleanFormula trueIntp=null;
  private   BooleanFormula errorIntp=null;

  private List<Pair<Boolean,String>> oprs=new ArrayList<Pair<Boolean,String>>();
  private List<List<String>> conds=null;
  private boolean isTrueFull = false;
  private boolean isErrorFull = false;
  private int weight=0;
  private boolean eIsEqSuc=false;
  private boolean sIsEqSuc=false;
  private boolean ec=true;
  private boolean sc=true;
  private int isKey=0;
  private boolean isEnd=false;
  private List<Pair<Integer, Integer>> which=null;
  private List<BooleanFormula> glbVarErrIntp=null;
  private Map<Integer,BooleanFormula> errIntp=new HashMap<Integer,BooleanFormula>(2);
  private Map<Integer,Set<List<BooleanFormula>>> errIntpForPrincess=new HashMap<Integer,Set<List<BooleanFormula>>>(2);
  private Map<Integer,List<BooleanFormula>> csGlbVarErrIntp=new HashMap<Integer,List<BooleanFormula>>(2);





  public Map<Integer, Set<List<BooleanFormula>>> getErrIntpForPrincess() {
    return errIntpForPrincess;
  }



  public void setErrIntpForPrincess(Map<Integer, Set<List<BooleanFormula>>> pErrIntpForPrincess) {
    errIntpForPrincess = pErrIntpForPrincess;
  }


  public Map<Integer, List<BooleanFormula>> getCsGlbVarErrIntp() {
    return csGlbVarErrIntp;
  }


  public void setCsGlbVarErrIntp(Map<Integer, List<BooleanFormula>> pCsGlbVarErrIntp) {
    csGlbVarErrIntp = pCsGlbVarErrIntp;
  }

 // public void addCsGlbVarErrIntp(int key, )

  public Map<Integer, BooleanFormula> getErrIntp() {
    return errIntp;
  }

  public void addErrIntp(int key, BooleanFormula value) {
    if(errIntp==null){
      errIntp=new HashMap<Integer,BooleanFormula>(2);
    }
    errIntp.put(key,value);
  }
  public void addGlbVarErrIntp(BooleanFormula fb){
    if(glbVarErrIntp==null){
      glbVarErrIntp=new ArrayList<BooleanFormula>(2);
    }
    glbVarErrIntp.add(fb);
  }
  public List<BooleanFormula> getGlbVarErrIntp() {
    return glbVarErrIntp;
  }


  public void setGlbVarErrIntp(List<BooleanFormula> glbVarErrIntp,List<BooleanFormula> pGlbVarErrIntp) {
    if(pGlbVarErrIntp!=null){
    if(glbVarErrIntp==null){
      glbVarErrIntp=new ArrayList<BooleanFormula>(2);
    }
    String s=glbVarErrIntp.toString();
    for(BooleanFormula bf : pGlbVarErrIntp){
      if(!s.contains(bf.toString())){
        glbVarErrIntp.add(bf);
      }
    }
    }
    else{
      if (!errorIntp.toString().contains("::")){
        if(glbVarErrIntp==null){
          glbVarErrIntp=new ArrayList<BooleanFormula>(2);
        }
        glbVarErrIntp.add(errorIntp);
      }
    }
  }

  public BooleanFormula getErrorIntp() {
    return errorIntp;
  }

  public void setErrorIntp(BooleanFormula pErrorIntp) {
    errorIntp = pErrorIntp;
  }
  public int isKey() {
    return isKey;
  }



  public void setKey(int pIsKey) {
    isKey = pIsKey;
  }



  public boolean isEnd() {
    return isEnd;
  }



  public void setEnd(boolean pIsEnd) {
    isEnd = pIsEnd;
  }


  public BooleanFormula getTrueIntp() {
    return trueIntp;
  }


  public void setTrueIntp(BooleanFormula pTrueIntp) {
    trueIntp = pTrueIntp;
  }


  public boolean isTrueFull() {
    return isTrueFull;
  }


  public void setTrueFull(boolean pIsTrueFull) {
    if(this.getNodeNumber()==1421&&pIsTrueFull){
      int d=1;
      d=d+1;
    }
    isTrueFull = pIsTrueFull;
  }


  public boolean isErrorFull() {
    return isErrorFull;
  }


  public void setErrorFull(boolean pIsErrorFull) {
    isErrorFull = pIsErrorFull;
  }


  public int getWeight() {
    return weight;
  }


  public void setWeight(int pWeight) {
    weight = pWeight;
  }


  public boolean iseIsEqSuc() {
    return eIsEqSuc;
  }


  public void seteIsEqSuc(boolean pEIsEqSuc) {
    eIsEqSuc = pEIsEqSuc;
  }


  public boolean issIsEqSuc() {
    return sIsEqSuc;
  }


  public void setsIsEqSuc(boolean pSIsEqSuc) {
    sIsEqSuc = pSIsEqSuc;
  }


  public boolean isEc() {
    return ec;
  }


  public void setEc(boolean pEc) {
    ec = pEc;
  }


  public boolean isSc() {
    return sc;
  }


  public void setSc(boolean pSc) {
    sc = pSc;
  }

  public CFANode(String pFunctionName) {
    assert !pFunctionName.isEmpty();

    functionName = pFunctionName;
    nodeNumber = idGenerator.getFreshId();
  }

  public int getNodeNumber() {
    return nodeNumber;
  }

  public int getReversePostorderId() {
    return reversePostorderId;
  }

  public void setReversePostorderId(int pId) {
    reversePostorderId = pId;
  }

  public void addLeavingEdge(CFAEdge pNewLeavingEdge) {
    checkArgument(pNewLeavingEdge.getPredecessor() == this,
        "Cannot add edge \"%s\" to node %s as leaving edge", pNewLeavingEdge, this);
    leavingEdges.add(pNewLeavingEdge);
  }

  public void removeLeavingEdge(CFAEdge pEdge) {
    boolean removed = leavingEdges.remove(pEdge);
    checkArgument(removed,
        "Cannot remove non-existing leaving edge \"%s\" from node %s", pEdge, this);
  }

  public int getNumLeavingEdges() {
    return leavingEdges.size();
  }

  public CFAEdge getLeavingEdge(int pIndex) {
    return leavingEdges.get(pIndex);
  }

  public void addEnteringEdge(CFAEdge pEnteringEdge) {
    checkArgument(pEnteringEdge.getSuccessor() == this,
        "Cannot add edge \"%s\" to node %s as entering edge", pEnteringEdge, this);
    enteringEdges.add(pEnteringEdge);
  }

  public void removeEnteringEdge(CFAEdge pEdge) {
    boolean removed = enteringEdges.remove(pEdge);
    checkArgument(removed,
        "Cannot remove non-existing entering edge \"%s\" from node %s", pEdge, this);
  }

  public int getNumEnteringEdges() {
    return enteringEdges.size();
  }

  public CFAEdge getEnteringEdge(int pIndex) {
    return enteringEdges.get(pIndex);
  }

  public CFAEdge getEdgeTo(CFANode pOther) {
    for (CFAEdge edge : leavingEdges) {
      if (edge.getSuccessor() == pOther) {
        return edge;
      }
    }

    throw new IllegalArgumentException("there is no edge from " + this + " to " + pOther);
  }

  public boolean hasEdgeTo(CFANode pOther) {
    boolean hasEdge = false;
    for (CFAEdge edge : leavingEdges) {
      if (edge.getSuccessor() == pOther) {
        hasEdge = true;
        break;
      }
    }

    return hasEdge;
  }

  public void setLoopStart() {
    isLoopStart = true;
  }

  public boolean isLoopStart() {
    return isLoopStart;
  }

  public String getFunctionName() {
    return functionName;
  }

  public void addEnteringSummaryEdge(FunctionSummaryEdge pEdge) {
    checkState(enteringSummaryEdge == null,
        "Cannot add two entering summary edges to node %s", this);
    enteringSummaryEdge = pEdge;
  }

  public void addLeavingSummaryEdge(FunctionSummaryEdge pEdge) {
    checkState(leavingSummaryEdge == null,
        "Cannot add two leaving summary edges to node %s", this);
    leavingSummaryEdge = pEdge;
  }

  public FunctionSummaryEdge getEnteringSummaryEdge() {
    return enteringSummaryEdge;
  }

  public FunctionSummaryEdge getLeavingSummaryEdge() {
    return leavingSummaryEdge;
  }

  public void removeEnteringSummaryEdge(FunctionSummaryEdge pEdge) {
    checkArgument(enteringSummaryEdge == pEdge,
        "Cannot remove non-existing entering summary edge \"%s\" from node \"%s\"", pEdge, this);
    enteringSummaryEdge = null;
  }

  public void removeLeavingSummaryEdge(FunctionSummaryEdge pEdge) {
    checkArgument(leavingSummaryEdge == pEdge,
        "Cannot remove non-existing leaving summary edge \"%s\" from node \"%s\"", pEdge, this);
    leavingSummaryEdge = null;
  }

  @Override
  public String toString() {
    return "N" + nodeNumber;
  }

  @Override
  public final int compareTo(CFANode pOther) {
    return Integer.compare(this.nodeNumber, pOther.nodeNumber);
  }

  @Override
  public final boolean equals(Object pObj) {
    // Object.equals() is consistent with our compareTo()
    // because nodeNumber is a unique identifier.
    return super.equals(pObj);
  }

  @Override
  public final int hashCode() {
    // Object.hashCode() is consistent with our compareTo()
    // because nodeNumber is a unique identifier.
    return super.hashCode();
  }

  /**
   * Return a human-readable string describing to which point in the program
   * this state belongs to.
   * Returns the empty string if no suitable description can be found.
   *
   * Normally CFANodes do not belong to a file location,
   * so this should be used only as a best-effort guess to give a user
   * at least something to hold on.
   * Whenever possible, use the file locations of edges instead.
   */
  public String describeFileLocation() {
    if (this instanceof FunctionEntryNode) {
      return "entry of function " + getFunctionName()
          + " in " + ((FunctionEntryNode)this).getFileLocation();
    }

    if (this instanceof FunctionExitNode) {
      // these nodes do not belong to a location
      return "exit of function " + getFunctionName()
          + " in " + ((FunctionExitNode)this).getEntryNode().getFileLocation();
    }

    if (getNumLeavingEdges() > 0) {
      CFAEdge edge = getLeavingEdge(0);

      if (!edge.getFileLocation().equals(FileLocation.DUMMY)) {
        return "before " + edge.getFileLocation();
      }
    }

    if (getNumEnteringEdges() > 0) {
      CFAEdge edge = getEnteringEdge(0);

      if (!edge.getFileLocation().equals(FileLocation.DUMMY)) {
        return "after " + edge.getFileLocation();
      }
    }

    return "";
  }

  public List<CFAEdge> getLeavingEdge() {
    // TODO Auto-generated method stub
    return leavingEdges;
  }
  public List<CFAEdge> getEnteringEdge() {
    // TODO Auto-generated method stub
    return enteringEdges;
  }

  public List<Pair<Integer, Integer>> getWhich() {
    return which;
  }

  public void addWhich(Pair<Integer, Integer> len) {
    if(which==null){
      which=new ArrayList<Pair<Integer, Integer>>(2);
    }
    which.add(len);
  }
  public List<List<String>> getConds() {
    return conds;
  }
  public void setConds(List<List<String>> pConds) {
    conds = pConds;
  }

  public void addConds(List<String> pCond) {
    if(conds==null){
      conds=new ArrayList<List<String>>();
    }
    conds.add(pCond);
  }
  public List<Pair<Boolean, String>> getOprs() {
    return oprs;
  }

  public void setOprs(List<Pair<Boolean, String>> pOprs) {
    oprs = pOprs;
  }


  public void setErrIntp(Map<Integer, BooleanFormula> pErrIntp) {
    // TODO Auto-generated method stub
    errIntp=pErrIntp;
  }
}
