/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2017  Dirk Beyer
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

import ap.CmdlMain;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Stack;

public class PrincessInfo {

  public static String[] opr = { "(+", "(-", "(*", "(/", "(and", "(or", "(not", "(=", "(<", "(>","(>=","(<=" };
  public static List<String> oprList = new ArrayList<String>();
  public static String x = "x";
  public static int count = 0;
  public static ByteArrayOutputStream baoStream = new ByteArrayOutputStream(1024);
  public static PrintStream cacheStream = new PrintStream(baoStream);
  public static int tmp=0;
  public static int fileNum=0;
  /*
   * convert BooleanFormula to the form of Princess and compute
   *
   * @para list: {edge, E-interp}
   */
  public static String analyzeUsePrincess(List<String> list,List<String> pFunc) throws IOException {
    setOperator();
    List<String> var1 = new ArrayList<String>();
    List<String> newName1 = new ArrayList<String>();
    String A = "";
    String B = "";
    String exp = list.get(0);
    //System.out.println(exp);
    if(canHandle(exp)){
      return "";
    }
    String ret1 = convert1(exp, var1, newName1);
    System.out.println("ret1=" + ret1);
    ret1=ret1.replaceAll("\\[","(");
    ret1=ret1.replaceAll("\\]",")");
    String r1Array[] = ret1.split(" ");
    List<String> r1List = Arrays.asList(r1Array);
    for (int i = 1; i < list.size(); i++) {
      exp = list.get(i);
      if(canHandle(exp)){
        return "";
      }
      List<String> var2 = new ArrayList<String>();
      List<String> newName2 = new ArrayList<String>();
      List<String> common = new ArrayList<String>();
      String ret2 = convert2(exp, var1, newName1, var2, newName2, common);
      //System.out.println("ret2=" + ret2);
      if(ret2.startsWith("[")) {
        ret2=ret2.substring(1,ret2.length()-1);
      }
      ret2=ret2.replaceAll("\\[","(");
      ret2=ret2.replaceAll("\\]",")");
      List<String> listTerm=new ArrayList<String>();
    listTerm.add(ret2);
    if(ret2.contains("and")||ret2.contains("or")){
      listTerm=term(ret2);
    }
    for(String ls: listTerm){
      ret2=ls;
      if(ret2.contains("[")){
       ret2=ret2.replaceAll("\\[", "\\(");
       ret2=ret2.replaceAll("\\]", "\\)");
       ret2=ret2.replaceAll("and", "&");
       ret2=ret2.replaceAll("or", "|");
      }
      String r2Array[] = ls.trim().split(" ");
        List<String> r2List = Arrays.asList(r2Array);
        StringBuilder problem = new StringBuilder();
        StringBuilder part2 = new StringBuilder();
        List<String> comVar=comVarOf(r2List,common);
      if (comVar.size() == 1) {    // y= x[+-*\]1; y>6  or   y= x+1; 6>y
            String cv = comVar.get(0);
            problem.append("\\forall int ");
            part2.append("\\exists int ");
            if (var1.size() == 2) {
              int oprIndex=-1;
              int remVIndex=-1;
              String glbV = "";
              int vsize1 = r1List.indexOf(cv);
              for (int j = 0; j < r1List.size(); j++) {
                String r = r1List.get(j).trim();
                System.out.println(r);
                if (oprList.contains("(" + r) && r.equals("=")) {
                  oprIndex=j;

                  if (vsize1 == 0) {
                    glbV = newName1.get(0);
                    break;
                  }
                }

              }
              if(glbV.equals("")){
                return "";
              }
              int vsize2 = r2List.indexOf(cv);
              int r2Size = r2List.size();
              for (int j = 0; j < r2Size; j++) {
                String r = r2List.get(j);
                if (oprList.contains("(" + r)) {
                  if(r.contains("<")||r.contains(">")){
                    if(r1List.get(r1List.indexOf(glbV)-1).equals("-")){
                      if(r.contains("<")){
                        r=r.replaceAll("<", ">");
                      }
                      else if(r.contains(">")){
                        r=r.replaceAll(">", "<");
                      }
                    }
                    if(!r.contains("=")){
                      r=r+"=";
                    }
                  }
                  if (j == vsize2 + 1) {
                    A = glbV + " " + r + " B";
                    System.out.println(A);
                    break;
                  } else if (j == vsize2 - 1) {
                    A = "B" + " " + r + " " + glbV;
                    System.out.println(A);
                    break;
                  }
                }
              }
              problem.append(glbV+"; ");
              problem.append("( " + A + " -> ");

              part2.append(cv+"; ");
              part2.append("( " + ret1 + " & " + ret2 + " )");
              problem.append(part2 + " )");
              System.out.println(problem);
              File file=new File("princess\\problem.pri");
              String part1="\\existentialConstants { \r\n int B; \r\n }";
              FileWriter fw=new FileWriter(file);
              fw.write(part1+"\r\n");
              fw.write("\\problem {\r\n");
              fw.write(problem.toString()+"\r\n");
              fw.write("}");
              fw.close();
              String[] arg={"+mostGeneralConstraint","princess\\problem.pri"};
              fileNum++;
              PrintStream oldStream = System.out;
              System.setOut(cacheStream);

              CmdlMain.main(arg);
              String message=baoStream.toString();
              System.setOut(oldStream);
              baoStream.reset();
              System.out.println("message:="+message);
              if(message.contains("Under the most-general constraint:")){
                String constraint=message.substring(message.indexOf("Under the most-general constraint:")+34);
                System.out.println(constraint);
                String oldName = var1.get(newName1.indexOf(glbV));
                if(oldName.contains("|")){
                  oldName=oldName.replaceAll("\\|", "");
                }
                String s[]=oldName.substring(0, oldName.indexOf("@")).split("::");
                String fs="";
                if(s.length==2){
                 fs = constraint.substring(0,constraint.indexOf("B"))+s[1]+constraint.substring(constraint.indexOf("B")+1);
                 pFunc.add(s[0]);
                 fs=fs.replaceAll("\r\n", "");
                 fs="int "+s[0]+"(){ \r\nint "+s[1]+"; \r\n if("+fs+"){\r\n"+s[1]+"="+s[1]+"+1;\r\n} \r\n}";
                }
                else{
                  fs=constraint.substring(0,constraint.indexOf("B"))+s[0]+constraint.substring(constraint.indexOf("B")+1);
                  pFunc.add("main");
                  fs=fs.replaceAll("\r\n", "");
                  fs="int "+s[0]+";\r\n"+"int main(){"+"\r\n if("+fs+"){\r\n"+s[0]+"="+s[0]+"+1;\r\n} \r\n}";
                }

                System.out.println(fs);
                return fs;
              }
            }
            return "";
          }
    }


      return "";
    }

    return "";
  }

  private static boolean canHandle(String exp) {
    // TODO Auto-generated method stub
    return exp.contains("distinct")||exp.contains("(let")||exp.contains("(*unsigned")||exp.contains("(*signed")||exp.contains("->")||exp.contains("{")||exp.contains("|*(");
  }

  private static List<String> comVarOf(List<String> r2List, List<String> common) {
    // TODO Auto-generated method stub
      List<String> list=new ArrayList<String>();
      for(int i=0;i<common.size();i++){
        String cv=common.get(i);
        if(r2List.contains(cv)){
          list.add(cv);
        }
      }
    return list;
  }

  public static String convert2(String exp, List<String> var1, List<String> newName1, List<String> var2,
        List<String> newName2, List<String> common) {
      String ret = "";
      if (!exp.equals("true")) {
        String sp[] = exp.split(" ");
        Stack<String> stack1 = new Stack<String>(); // for operator
        //Stack<String> stack2 = new Stack<String>(); // for operand

        for (int i = 0; i < sp.length; i++) {
          String ele = sp[i];
          if (oprList.contains(ele)) {
           //ele = ele.substring(1);
            stack1.push(ele);
          } else {
            //ele = ele.replaceAll("[\\(\\)]", "");
            stack1.push(ele);
            if(ele.contains(")")){
              int numRightBracket=0;
              for(int j=0;j<ele.length();j++){
                if(ele.charAt(j)==')'){
                  numRightBracket++;
                }
              }

              while(numRightBracket!=0){
                String op2 = stack1.pop();
                op2=op2.replaceAll("\\)", "");
                if (var1.contains(op2)) {
                  op2 = newName1.get(var1.indexOf(op2));
                  common.add(op2);
                } else if (op2.contains("@") && !var2.contains(op2)) {
                  var2.add(op2);
                  op2 = x + (count++);
                  newName2.add(op2);
                } else if (op2.contains("@") && var2.contains(op2)) {
                  op2 = newName2.get(var2.indexOf(op2));
                }
                String op1 = stack1.pop();
                String op="";
                String opr="";
                if(op1.contains("(")){
                  if(op1.equals("(-")) {
                    opr = "[ -" + op2+" ]";
                  }
                  else if(op1.equals("(not")){
                    opr="(! [ "+op2+" ]";
                  }
                }
                else{
                  if (var1.contains(op1)) {
                    // common.add(op1);
                    op1 = newName1.get(var1.indexOf(op1));
                    if(!common.contains(op1)) {
                      common.add(op1);
                    }
                  } else if (op1.contains("@") && !var2.contains(op1)) {
                    var2.add(op1);
                    op1 = x + (count++);
                    newName2.add(op1);
                  } else if (op1.contains("@") && var2.contains(op1)) {
                    op1 = newName2.get(var2.indexOf(op1));
                  }
                 op = stack1.pop();
                 opr = op1 + " " + op + " " + op2;
                 if(op.contains("and")||op.contains("or")){
                   opr="[ "+opr+" ]";
                 }
                }
                opr=opr.replaceAll("[\\(\\)]", "");
                stack1.push(opr);
                numRightBracket--;
              }
            }

          }
        }
        ret = stack1.pop();
        ret=ret.replaceAll("[\\(\\)]","");
      }
      return ret;
    }

    public static String convert1(String exp, List<String> var, List<String> newName) {
      String ret = "";
      if (!exp.equals("true")) {
        String sp[] = exp.split(" ");
        Stack<String> stack1 = new Stack<String>(); // for operator
        //Stack<String> stack2 = new Stack<String>(); // for operand

        for (int i = 0; i < sp.length; i++) {
          String ele = sp[i];
          if (oprList.contains(ele)) {
           //ele = ele.substring(1);
            stack1.push(ele);
          } else {
            //ele = ele.replaceAll("[\\(\\)]", "");
            stack1.push(ele);
            if(ele.contains(")")){
              int numRightBracket=0;
              for(int j=0;j<ele.length();j++){
                if(ele.charAt(j)==')'){
                  numRightBracket++;
                }
              }

              while(numRightBracket!=0){
                String op2 = stack1.pop();
                op2=op2.replaceAll("\\)", "");
                if (op2.contains("@") && !var.contains(op2)) {
                  var.add(op2);
                  op2 = x + (count++);
                  newName.add(op2);
                } else if (op2.contains("@") && var.contains(op2)) {
                  op2 = newName.get(var.indexOf(op2));
                }
                String op1 = stack1.pop();
                String op="";
                String opr="";
                if(op1.contains("(")){
                  if(op1.equals("(not")){
                    opr="(! [ "+op2+" ]";
                  }
                  else{
                    opr = op1 + op2;
                  }
                }
                else{
                  if (op1.contains("@") && !var.contains(op1)) {
                    var.add(op1);
                    op1 = x + (count++);
                    newName.add(op1);
                  } else if (op1.contains("@") && var.contains(op1)) {
                    op1 = newName.get(var.indexOf(op1));
                  }
                 op = stack1.pop();
                 opr = op1 + " " + op + " " + op2;
                }
                stack1.push(opr);
                numRightBracket--;
              }
            }

          }
        }
        ret = stack1.pop();
        ret=ret.replaceAll("[\\(\\)]","");
      }
      return ret;
    }

    public static void setOperator() {

      for (int i = 0; i < opr.length; i++) {
        oprList.add(opr[i]);
      }
    }
    public static List<String> term(String exp){
      Stack<String> stack = new Stack<String>();
      String [] arr = exp.split(" ");
      String firstOpr="";
      int numleftBracket=0;
      String op1="";
      String op2="";
      int mainOpr=0;
      for(int i=0;i<arr.length;i++){
        String s = arr[i];
        if(s.equals("[")){
          numleftBracket++;
        }
        else if(s.equals("]")){
          numleftBracket--;
        }
        else if(s.equals("or")&&numleftBracket==0){
          op2=subString(arr,i+1,arr.length);
          mainOpr=1;
          break;
        }
        else if(s.equals("and")&&numleftBracket==0){
          op2=subString(arr,i+1,arr.length);
          mainOpr=2;
          break;
        }
        op1+=s+" ";
      }
      System.out.println("op1="+op1+"****"+"op2="+op2);
      List<String> list =new ArrayList<String>();
      if(mainOpr==1){
        list.add(op1);
        list.add(op2);
      }
      else if(mainOpr==2){
        op1 = op1 + " & " +op2;
        op1 = op1.replaceAll("and", "&");
        op1 = op1.replaceAll("or", "|");
      }
      return list;
    }
    public static String subString(String[] arr, int start, int end){
    if(start<0||end>arr.length){
      return "";
    }
    String ret="";
    for(int i=start;i<end;i++){
      String ele = arr[i];
      ret+=ele+" ";
    }
    return ret;

    }

}
