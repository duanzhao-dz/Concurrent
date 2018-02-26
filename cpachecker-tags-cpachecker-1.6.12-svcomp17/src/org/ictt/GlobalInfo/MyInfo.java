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

import com.google.common.base.Splitter;
import java.io.IOException;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CFACreator;
import org.sosy_lab.cpachecker.cfa.Parser;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.pathformula.pointeraliasing.PointerTargetSet;

public class MyInfo {

  public static LogManager logger;
  public static Configuration config;
  public static ShutdownNotifier shutdownNotifier;
  //public static MainCPAStatistics stats;
  public static Parser parser=null;
  public static boolean noPreprocess=true;
  public static boolean nonExportCFA=false;
  public static CtoFormulaConverter converter=null;
  public static PointerTargetSet pts=null;
  public static PathFormula lastOldFormula=null;
  public static String pcName="";
  public static CFA parse(String program,String func) throws InvalidConfigurationException,
  IOException,
  ParserException, InterruptedException {
// parse file and create CFA
 noPreprocess = false;
CFACreator cfaCreator = new CFACreator(config, logger, shutdownNotifier);
cfaCreator.setMainFunctionName(func);
//stats.setCFACreator(cfaCreator);
MyInfo.nonExportCFA =true;
Splitter commaSplitter = Splitter.on(',').omitEmptyStrings().trimResults();
CFA cfa = cfaCreator.parseSourceAndCreateCFA(program);//parseFileAndCreateCFA(commaSplitter.splitToList(fileNamesCommaSeparated));
///stats.setCFA(cfa);
return cfa;
}
}
