/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.ictt.GlobalInfo;

import com.google.common.collect.ImmutableList;
import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CLabelNode;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Refiner;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGPath;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaTypeHandler;
import org.sosy_lab.cpachecker.util.predicates.smt.BooleanFormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class SymInfo {
	public static ARGPath path = null;
	public static AbstractState state = null;
	public static boolean spurious = false;
	public static boolean isSat = true;
	public static BooleanFormulaManagerView bfmr;
	public static CtoFormulaTypeHandler typeHandler;
	public static SSAMap ssa;
	public static boolean isTermimal = false;
	public static HashMap<String, String> Vars = null;
	public static HashMap<String, Integer> ssaTemp;
	public static Result result = Result.UNKNOWN;
	public static int count = 0;
	public static List<BooleanFormula> pathFormula = new ArrayList<BooleanFormula>();
	public static List<Integer> states = new ArrayList<Integer>();
	public static List<Integer> branchStateLoc = new ArrayList<Integer>();
	public static BooleanFormula curFor = null;
	public static ReachedSet reached = null;
	public static ARGState furState = null;
	public static long time = 0;
	public static int num = 0;
	public static int usetime = 0;
	public static long uT = 0;
	public static boolean tmp1 = false;
	public static CFANode errBra = null;
	public static Set<Integer> errBras = new HashSet<Integer>(4);
	public static Set<Integer> bugState = new HashSet<Integer>();
	public static boolean hasRefine = false;
	public static boolean isStop = false;
	// public static boolean isIntpRef=false;
	public static int size = -1;
	// public static Set<Integer> changed=new HashSet<Integer>();
	public static Set<Integer> keyNode = new HashSet<Integer>();
	public static int tR;
	public static ARGState ffState = null;
	public static int refine = 0;
    public static Set<Integer> nodeIds=new HashSet<Integer>();
    public static boolean weight=false;
    //2016.12.15   can be removed
    public static File file= new File("Output1.txt");
    public static int sum=0;
    public static boolean useErr=false;
    public static Set<String> pathHash=new HashSet<String>();
    public static String curHash="";
    public static List<Integer> braIds=new ArrayList<Integer>(); //record the index of branch in a counterexample path
    public static int lastFalse=-1;
    public static boolean testintep=false;
    public static int TMPTIME=0;
	public static boolean repeatCE=false;
	public static int firstCE=0;
	public static StringBuilder chBras = new StringBuilder("");
	public static int curLocId=-1;
	public static boolean curSameE=false;
	public static boolean sucSameE=false;
	public static boolean curSameS=false;
	public static boolean sucSameS=false;
	public static CFANode curLoc;
	public static boolean useError=false;
	public static boolean useSafety=false;
	public static int model=0;
	public static BooleanFormula nextIntp=null;
	public static boolean hasFindFalse=false;
	public static int curLen=-1;
	public static int maxPL=-1;
	public static int tmpCond=0;
	public static Refiner mRefiner;
	public static BooleanFormula curTIntpF=null;
	public static boolean notFirst=false;
	public static Set<Integer> ceLoc=new HashSet<Integer>();
	public static ARGState nfindLocS=null;
	public static boolean testTmp1=false;
  public static Set<Integer> onePL=new HashSet<Integer>();
  public static boolean forUninstance=false;
  /***for error interploant***/
  public static Map<String,Integer> callstack=new HashMap<String,Integer>();
  public static int countNumCallstack=0;
  //public static int curSucCallStack=0;
  public static String curSucCallStack="";
  /******can remove *********/
  public static StringBuilder sb;

  /****************/
  /******for Chaojie Li*********/
  public static List<String> errorPath = new ArrayList<String>();
  public static boolean realErrPath = false;
  /****************************/

//  public static List<BooleanFormula> cePF = new ArrayList<BooleanFormula>();
//  public static List<List<BooleanFormula>> mayCE=new ArrayList<List<BooleanFormula>>();
//  public static int sub=0;
	public static boolean isTrueFull(CFANode loc) {
		// TODO Auto-generated method stub
		List<CFAEdge> edges = loc.getLeavingEdge();
		if (edges == null) {
			return true;
		}
		for (CFAEdge e : edges) {
			if (e instanceof CFunctionSummaryStatementEdge) {
				continue;
			}
			if (!e.isUsed()) {
				continue;
			}
			CFANode suc = e.getSuccessor();
			if (!suc.isTrueFull()) {
				return false;
			}
		}
		return true;
	}

	public static boolean isErrorFull(CFANode loc) {
		// TODO Auto-generated method stub
		List<CFAEdge> edges = loc.getLeavingEdge();
		if (edges == null) {
			return true;
		}
		for (CFAEdge e : edges) {
			if (e instanceof CFunctionSummaryStatementEdge) {
				continue;
			}
			if (!e.isUsed()) {
				continue;
			}
			CFANode suc = e.getSuccessor();
			if (!suc.isErrorFull()) {
				return false;
			}
		}
		return true;
	}

	public static boolean iskey(CFANode loc) {
		// TODO Auto-generated method stub
		List<CFAEdge> edges = loc.getLeavingEdge();
		if (edges == null) {
			return true;
		}
		for (CFAEdge e : edges) {
			CFANode suc = e.getSuccessor();
			if (suc.isKey() != -1) {
				return false;
			}
		}
		return true;
	}

	public static Set<ARGState> labelRemainStates(Set<ARGState> subgraph,
			ARGState lastState) {
		// TODO Auto-generated method stub
		ARGState target = null;
		Set<ARGState> hasHandle = new HashSet<ARGState>();
		ARGState parent = lastState.getParents().iterator().next();

		while (parent != furState) {
			// hasHandle.add(parent);
			CFANode pLoc = parent.getLoc();
			if (errBras.contains(pLoc.getNodeNumber())) {
				target = parent;
				break;
			}

			parent = parent.getParents().iterator().next();
		}
		if (target != null) {
			parent = target;
			while (parent != furState) {
				hasHandle.add(parent);
				parent = parent.getParents().iterator().next();
			}
			hasHandle.add(furState);
			hasHandle.addAll(target.getChildren());
			return hasHandle;
		}
		return null;
	}

	public static void findUselessEdges() {
		// TODO Auto-generated method stub
		if (errBra != null) {
			Stack<CFANode> stack = new Stack<CFANode>();
			stack.push(errBra);
			while (!stack.isEmpty()) {
				CFANode top = stack.pop();
				List<CFAEdge> enter = top.getEnteringEdge();
				for (CFAEdge edge : enter) {
					if (!edge.isUsed()) {
						edge.setUsed(true);
						CFANode pre = edge.getPredecessor();
						stack.add(pre);
						if(edge instanceof CAssumeEdge){
							((CAssumeEdge) edge).setTof(((CAssumeEdge) edge).getTruthAssumption());
						}
					}

				}
			}
		}
	}

	public static void removeUnReach(ReachedSet reachedSet) {
		// TODO Auto-generated method stub
		if (/* SymInfo.unreach && */SymInfo.furState != null) {
			if (!SymInfo.furState.isDestroyed()) {
				ARGState parent = SymInfo.furState.getParents().iterator()
						.next();
				parent.setMycover(false);
				Set<ARGState> subgraph = SymInfo.furState.getSubgraph();
				if (subgraph != null) {
					Iterator<ARGState> it = subgraph.iterator();
					while (it.hasNext()) {
						ARGState next = it.next();
						if (reachedSet.getWaitlist().contains(next)
								&& !subgraph.containsAll(next.getParents())) {
							continue;
						}
						next.removeFromARG();
						reachedSet.remove(next);
					}
				}
				reachedSet.remove(SymInfo.furState);
				SymInfo.furState.removeFromARG();
			}
		}
		SymInfo.furState = null;
	}

	public static void labelSafePath(ARGState state) {
		// TODO Auto-generated method stub
		ARGPath path = ARGUtils.getOnePathTo(state);
		// System.out.println(path);
		ImmutableList<ARGState> list = path.asStatesList();
		int lsize = list.size();
		// ARGState lastState = list.get(lsize - 1);
		CFANode lloc = state.getLoc();
		if (lloc == null) {
			lloc = AbstractStates.extractLocation(state);
			state.setLoc(lloc);
		}
		boolean truEnd = false;
		ARGState next=null;
		boolean change=true;
		for (int i = lsize - 1; i >= 1 &&(change ||!truEnd); i--) {
			ARGState s = list.get(i);
			ARGState pre = list.get(i-1);
			CFANode loc = s.getLoc();
			if(i!=lsize-1) {
        next=list.get(i+1);
      }
			int ow=loc.getWeight();
			List<CFAEdge> edge = pre.getEdgesToChild(s);
			boolean curIsFull=loc.isTrueFull();
			if (!curIsFull && !isTrueFull(loc)) {
				if(loc.isLoopStart()&&!(loc instanceof CLabelNode)&&next!=null ){

					 if(edge.get(0) instanceof CAssumeEdge ){
						 if(!((CAssumeEdge)edge.get(0)).getTruthAssumption()&&next.getLoc().isTrueFull()){
							 loc.setTrueFull(true);
							 for(int j=0;j<edge.size();j++){
							  edge.get(j).setWeight(0);
							 }
						 }
						 else{
							 truEnd = true;
							 if(change) {
                setWeight(s,next,edge);
              }
							 loc.setTrueFull(false);
						 }
					 }
					 else{
						 truEnd = true;
						 if(change) {
              setWeight(s,next,edge);
            }
						 loc.setTrueFull(false);
					 }
				}
				else{
					if (loc.getNumLeavingEdges() > 1
							&& loc.getLeavingEdge(0) instanceof CAssumeEdge) {
						truEnd = true;
					}
					if(change&&next!=null) {
					  setWeight(s,next,edge);
          }
					loc.setTrueFull(false);
				}
			} else {
				if(curIsFull){
					break;
				}
				if(next!=null){
				if(change) {
				  for(int j=0;j<edge.size();j++){
            edge.get(j).setWeight(0);
           }
        }
				if(SymInfo.weight&&edge.get(0) instanceof CAssumeEdge){
					Collections.sort(loc.getLeavingEdge(),
							new Comparator<CFAEdge>() {
								@Override
								public int compare(CFAEdge e1,
										CFAEdge e2) {
									Integer w1 = e1.getWeight()==-1?1:e1.getWeight();
									Integer w2 = e2.getWeight()==-1?1:e2.getWeight();
									return w1.compareTo(w2);
								}
							});
				}
				}
				loc.setTrueFull(true);
				List<CFAEdge> edges = pre.getEdgesToChild(s);
        for(int j=0;i<edges.size();j++){
          CFAEdge eth = edges.get(j);
          eth.getSuccessor().setTrueFull(true);
         }
			}
			next=s;
			if(ow==loc.getWeight()){
				change=false;
			}
		}

	}

	public static boolean forLoopNode(CFANode loc, CFANode nextLoc,
			ARGState curState, ARGState sucState) {
		// TODO Auto-generated method stub
		Collection<ARGState> children = curState.getChildren();
		CAssumeEdge e = (CAssumeEdge) loc.getEdgeTo(nextLoc);
		if (!e.getTruthAssumption()) {
			Iterator<ARGState> it = children.iterator();
			ARGState other = null;
			while (it.hasNext()) {
				ARGState next = it.next();
				if (next.getStateId() != sucState.getStateId()) {
					other = next;
					break;
				}
			}
			if (other != null) {
				PredicateAbstractState element = PredicateAbstractState
						.getPredicateState(other);
				BooleanFormula tf = element.getAbstractionFormula().asFormula();
				if (tf.toString().equals("false")) {
					return true;
				}
			}
		}
		return false;

	}

	public static void setWeight(ARGState cur, ARGState next, List<CFAEdge> pEdge) {
		// TODO Auto-generated method stub
        //compute the weight on e1
		List<CFAEdge> e = cur.getEdgesToChild(next);
		List<CFAEdge> lEdges = cur.getLoc().getLeavingEdge();
		int weight = 0;
		if(cur.getLoc().isTrueFull()){
		  for(int i=0;i<pEdge.size();i++) {
        pEdge.get(i).setWeight(0);
      }
		}
		if (e.size()==1&& e.get(0) instanceof CAssumeEdge) {

			for (CFAEdge le : lEdges) {
				if (le.getWeight() == -1) {
					weight += 1;
				} else {
					weight += le.getWeight();
				}
			}
			for(int i=0;i<pEdge.size();i++) {
        pEdge.get(i).setWeight(weight);
      }

	    Collections.sort(cur.getLoc().getLeavingEdge(), new Comparator<CFAEdge>() {
	        @Override
	        public int compare(CFAEdge e1, CFAEdge e2) {
	          Integer w1 = e1.getWeight()==-1?1:e1.getWeight();
	          Integer w2 = e2.getWeight()==-1?1:e2.getWeight();
	          return w1.compareTo(w2);
	        }
	      });

		} else {
			weight = e.get(0).getWeight();
			for(int i=0;i<pEdge.size();i++) {
        pEdge.get(i).setWeight(weight);
      }
		}
		//System.out.println(weight);


	}

	public static boolean useSInterpolant(CFANode location,
			BooleanFormula errorF, BooleanFormula trueF,
			ProverEnvironment myEnv, FormulaManagerView fmgr, SSAMap ssa) throws SolverException, InterruptedException {
		boolean isOK = false;
		if (errorF != null && !errorF.toString().equals("true")
				&& !errorF.toString().equals("false")) {
			errorF = fmgr.instantiate(errorF, ssa);
			if (SymInfo.pathFormula != null) {
				for (BooleanFormula pf : SymInfo.pathFormula) {
					myEnv.push(pf);
				}
			}
			isOK = true;
			myEnv.push(errorF);
			boolean b = myEnv.isUnsat();
			if (!b) {
				SymInfo.result = Result.FALSE;
                return true;
			}
			myEnv.pop();

		}
		if (location.isTrueFull()&&trueF != null && !trueF.toString().equals("true")
				&& !trueF.toString().equals("false")) {
			BooleanFormula tmpTrueF = fmgr.instantiate(trueF, ssa);
			if (SymInfo.pathFormula != null && !isOK) {
				for (BooleanFormula pf : SymInfo.pathFormula) {
					myEnv.push(pf);
				}
			}
			myEnv.push(tmpTrueF);
			boolean b = myEnv.isUnsat();
			if (!b) {
				myEnv.pop();
				tmpTrueF = fmgr.makeNot(tmpTrueF);
				myEnv.push(tmpTrueF);
				if (myEnv.isUnsat()) {
					SymInfo.isTermimal = true;
					myEnv.close();
					return true;
				}
			}

		}
		return false;
	}
}
