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
package org.sosy_lab.cpachecker.util.predicates.interpolation;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.cpachecker.util.statistics.StatisticsUtils.div;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.Iterables;
import com.google.common.util.concurrent.ThreadFactoryBuilder;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import org.ictt.GlobalInfo.MyInfo;
import org.ictt.GlobalInfo.PrincessInfo;
import org.ictt.GlobalInfo.SymInfo;
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.configuration.TimeSpanOption;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CLiteralExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CLabelNode;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException.Reason;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCCodeException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCFAEdgeException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.Triple;
import org.sosy_lab.cpachecker.util.VariableClassification;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.ITPStrategy;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.NestedInterpolation;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.SequentialInterpolation;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.SequentialInterpolationWithSolver;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.TreeInterpolation;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.TreeInterpolationWithSolver;
import org.sosy_lab.cpachecker.util.predicates.interpolation.strategy.WellScopedInterpolation;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ErrorConditions;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.Constraints;
import org.sosy_lab.cpachecker.util.predicates.pathformula.pointeraliasing.PointerTargetSetBuilder;
import org.sosy_lab.cpachecker.util.predicates.smt.BooleanFormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.cpachecker.util.statistics.StatisticsWriter;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;


@Options(prefix="cpa.predicate.refinement")
public final class InterpolationManager {

  private final Timer cexAnalysisTimer = new Timer();
  private final Timer satCheckTimer = new Timer();
  private final Timer getInterpolantTimer = new Timer();
  private final Timer cexAnalysisGetUsefulBlocksTimer = new Timer();
  private final Timer interpolantVerificationTimer = new Timer();
  private int reusedFormulasOnSolverStack = 0;

  public void printStatistics(StatisticsWriter w0) {
    w0.put("Counterexample analysis", cexAnalysisTimer + " (Max: " + cexAnalysisTimer.getMaxTime().formatAs(TimeUnit.SECONDS) + ", Calls: " + cexAnalysisTimer.getNumberOfIntervals() + ")");
    StatisticsWriter w1 = w0.beginLevel();
    if (cexAnalysisGetUsefulBlocksTimer.getNumberOfIntervals() > 0) {
      w1.put("Cex.focusing", cexAnalysisGetUsefulBlocksTimer + " (Max: " + cexAnalysisGetUsefulBlocksTimer.getMaxTime().formatAs(TimeUnit.SECONDS) + ")");
    }
    w1.put("Refinement sat check", satCheckTimer);
    if (reuseInterpolationEnvironment && satCheckTimer.getNumberOfIntervals() > 0) {
      w1.put("Reused formulas on solver stack", reusedFormulasOnSolverStack + " (Avg: " + div(reusedFormulasOnSolverStack, satCheckTimer.getNumberOfIntervals()) + ")");
    }
    w1.put("Interpolant computation", getInterpolantTimer);
    if (interpolantVerificationTimer.getNumberOfIntervals() > 0) {
      w1.put("Interpolant verification", interpolantVerificationTimer);
    }
  }


  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final FormulaManagerView fmgr;
  private final BooleanFormulaManagerView bfmgr;
  private final PathFormulaManager pmgr;
  private final Solver solver;

  private final Interpolator<?> interpolator;

  @Option(secure=true, description="apply deletion-filter to the abstract counterexample, to get "
    + "a minimal set of blocks, before applying interpolation-based refinement")
  private boolean getUsefulBlocks = false;

  @Option(secure=true, name="incrementalCexTraceCheck",
      description="use incremental search in counterexample analysis, "
        + "to find the minimal infeasible prefix")
  private boolean incrementalCheck = false;

  @Option(secure=true, name="cexTraceCheckDirection",
      description="Direction for doing counterexample analysis: from start of trace, from end of trace, or alternatingly from start and end of the trace towards the middle")
  private CexTraceAnalysisDirection direction = CexTraceAnalysisDirection.FORWARDS;

  @Option(secure=true, description="Strategy how to interact with the intepolating prover. " +
          "The analysis must support the strategy, otherwise the result will be useless!" +
          "\n- SEQ_CPACHECKER: We simply return each interpolant for i={0..n-1} for the partitions A=[0 .. i] and B=[i+1 .. n]. " +
          "The result is similar to INDUCTIVE_SEQ, but we do not guarantee the 'inductiveness', " +
          "i.e. the solver has to generate nice interpolants itself. Supported by all solvers!" +
          "\n- INDUCTIVE_SEQ: Generate an inductive sequence of interpolants the partitions [1,...n]. " +
          "\n- TREE: use the tree-interpolation-feature of a solver to get interpolants" +
          "\n- TREE_WELLSCOPED: We return each interpolant for i={0..n-1} for the partitions " +
          "A=[lastFunctionEntryIndex .. i] and B=[0 .. lastFunctionEntryIndex-1 , i+1 .. n]. Based on a tree-like scheme." +
          "\n- TREE_NESTED: use callstack and previous interpolants for next interpolants (see 'Nested Interpolants')," +
          "\n- TREE_CPACHECKER: similar to TREE_NESTED, but the algorithm is taken from 'Tree Interpolation in Vampire'.")
  private InterpolationStrategy strategy = InterpolationStrategy.SEQ_CPACHECKER;
  private static enum InterpolationStrategy {
    SEQ, SEQ_CPACHECKER,
    TREE, TREE_WELLSCOPED, TREE_NESTED, TREE_CPACHECKER}

  @Option(secure=true, description="dump all interpolation problems")
  private boolean dumpInterpolationProblems = false;

  @Option(secure=true, description="verify if the interpolants fulfill the interpolant properties")
  private boolean verifyInterpolants = false;

  @Option(secure=true, name="timelimit",
      description="time limit for refinement (use milliseconds or specify a unit; 0 for infinite)")
  @TimeSpanOption(codeUnit=TimeUnit.MILLISECONDS,
      defaultUserUnit=TimeUnit.MILLISECONDS,
      min=0)
  private TimeSpan itpTimeLimit = TimeSpan.ofMillis(0);

  @Option(secure=true, description="skip refinement if input formula is larger than "
    + "this amount of bytes (ignored if 0)")
  private int maxRefinementSize = 0;

  @Option(secure=true, description="Use a single SMT solver environment for several interpolation queries")
  private boolean reuseInterpolationEnvironment = false;

  private final ExecutorService executor;
  private final LoopStructure loopStructure;
  private final VariableClassification variableClassification;

  public InterpolationManager(
      PathFormulaManager pPmgr,
      Solver pSolver,
      Optional<LoopStructure> pLoopStructure,
      Optional<VariableClassification> pVarClassification,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) throws InvalidConfigurationException {
    config.inject(this, InterpolationManager.class);

    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
    fmgr = pSolver.getFormulaManager();
    bfmgr = fmgr.getBooleanFormulaManager();
    pmgr = pPmgr;
    solver = pSolver;
    loopStructure = pLoopStructure.orElse(null);
    variableClassification = pVarClassification.orElse(null);

    if (itpTimeLimit.isEmpty()) {
      executor = null;
    } else {
      // important to use daemon threads here, because we never have the chance to stop the executor
      executor =
          Executors.newSingleThreadExecutor(new ThreadFactoryBuilder().setDaemon(true).build());
    }

    if (reuseInterpolationEnvironment) {
      interpolator = new Interpolator<>();
    } else {
      interpolator = null;
    }
  }

  /**
   * Counterexample analysis.
   * This method is just an helper to delegate the actual work
   * This is used to detect timeouts for interpolation
   *
   * @param pFormulas the formulas for the path
   * @param pAbstractionStates the abstraction states between the formulas and the last state of the path.
   *                           The first state (root) of the path is missing, because it is always TRUE.
   *                           (can be empty, if well-scoped interpolation is disabled or not required)
   * @param elementsOnPath the ARGElements on the path (may be empty if no branching information is required)
   */
  public CounterexampleTraceInfo buildCounterexampleTrace(
      final List<BooleanFormula> pFormulas,
      final List<AbstractState> pAbstractionStates,
      final Set<ARGState> elementsOnPath,
      final boolean computeInterpolants) throws CPAException, InterruptedException {

    assert pAbstractionStates.isEmpty() || pFormulas.size() == pAbstractionStates.size();

    // if we don't want to limit the time given to the solver
    if (itpTimeLimit.isEmpty()) {
      return buildCounterexampleTrace0(pFormulas, pAbstractionStates, elementsOnPath, computeInterpolants);
    }

    assert executor != null;

    Callable<CounterexampleTraceInfo> tc = new Callable<CounterexampleTraceInfo>() {
      @Override
      public CounterexampleTraceInfo call() throws CPAException, InterruptedException {
        return buildCounterexampleTrace0(pFormulas, pAbstractionStates, elementsOnPath, computeInterpolants);
      }
    };

    Future<CounterexampleTraceInfo> future = executor.submit(tc);

    try {
      // here we get the result of the post computation but there is a time limit
      // given to complete the task specified by timeLimit
      return future.get(itpTimeLimit.asNanos(), TimeUnit.NANOSECONDS);

    } catch (TimeoutException e) {
      logger.log(Level.SEVERE, "SMT-solver timed out during interpolation process");
      throw new RefinementFailedException(Reason.TIMEOUT, null);

    } catch (ExecutionException e) {
      Throwable t = e.getCause();
      Throwables.propagateIfPossible(t, CPAException.class, InterruptedException.class);

      throw new UnexpectedCheckedException("interpolation", t);
    }
  }

  public CounterexampleTraceInfo buildCounterexampleTrace(
      final List<BooleanFormula> pFormulas,
      final List<AbstractState> pAbstractionStates,
      final Set<ARGState> elementsOnPath) throws CPAException, InterruptedException {
    return buildCounterexampleTrace(pFormulas, pAbstractionStates, elementsOnPath, true);
  }

  public CounterexampleTraceInfo buildCounterexampleTrace(
          final List<BooleanFormula> pFormulas) throws CPAException, InterruptedException {
    return buildCounterexampleTrace(
            pFormulas, Collections.<AbstractState>emptyList(), Collections.<ARGState>emptySet(), true);
  }

  private CounterexampleTraceInfo buildCounterexampleTrace0(
      final List<BooleanFormula> pFormulas,
      final List<AbstractState> pAbstractionStates,
      final Set<ARGState> elementsOnPath,
      final boolean computeInterpolants) throws CPAException, InterruptedException {

    logger.log(Level.FINEST, "Building counterexample trace");
    cexAnalysisTimer.start();
    try {

      // Final adjustments to the list of formulas
      List<BooleanFormula> f = new ArrayList<>(pFormulas); // copy because we will change the list

      if (fmgr.useBitwiseAxioms()) {
        addBitwiseAxioms(f);
      }

      f = Collections.unmodifiableList(f);
      logger.log(Level.ALL, "Counterexample trace formulas:", f);

      // now f is the DAG formula which is satisfiable iff there is a
      // concrete counterexample


      // Check if refinement problem is not too big
      if (maxRefinementSize > 0) {
        int size = fmgr.dumpFormula(bfmgr.and(f)).toString().length();
        if (size > maxRefinementSize) {
          logger.log(Level.FINEST, "Skipping refinement because input formula is", size, "bytes large.");
          throw new RefinementFailedException(Reason.TooMuchUnrolling, null);
        }
      }

      final Interpolator<?> currentInterpolator;
      if (reuseInterpolationEnvironment) {
        currentInterpolator = checkNotNull(interpolator);
      } else {
        currentInterpolator = new Interpolator<>();
      }

      try {
        try {
          return currentInterpolator.buildCounterexampleTrace(f, pAbstractionStates, elementsOnPath, computeInterpolants);
        } finally {
          if (!reuseInterpolationEnvironment) {
            currentInterpolator.close();
          }
        }
      } catch (SolverException itpException) {
        logger.logUserException(
            Level.FINEST,
            itpException,
            "Interpolation failed, attempting to solve without interpolation");
        return fallbackWithoutInterpolation(elementsOnPath, f, itpException);
      }

    } finally {
      cexAnalysisTimer.stop();
    }
  }

  /**
   * Attempt to check feasibility of the current counterexample without interpolation
   * in case of a failure with interpolation.
   * Maybe the solver can handle the formulas if we do not attempt to interpolate
   * (this happens for example for MathSAT).
   * If solving works but creating the model for the error path not,
   * we at least return an empty model.
   */
  private CounterexampleTraceInfo fallbackWithoutInterpolation(
      final Set<ARGState> elementsOnPath, List<BooleanFormula> f, SolverException itpException)
      throws InterruptedException, CPATransferException, RefinementFailedException {
    try (ProverEnvironment prover = solver.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      for (BooleanFormula block : f) {
        prover.push(block);
      }
      if (!prover.isUnsat()) {
        try {
          return getErrorPath(f, prover, elementsOnPath);
        } catch (SolverException modelException) {
          logger.log(
              Level.WARNING,
              "Solver could not produce model, variable assignment of error path can not be dumped.");
          logger.logDebugException(modelException);
          return CounterexampleTraceInfo.feasible(
              f, ImmutableList.<ValueAssignment>of(), ImmutableMap.<Integer, Boolean>of());
        }
      }
    } catch (SolverException solvingException) {
      // in case of exception throw original one below but do not forget e2
      itpException.addSuppressed(solvingException);
    }
    throw new RefinementFailedException(Reason.InterpolationFailed, null, itpException);
  }

  /**
   * Add axioms about bitwise operations to a list of formulas, if such operations
   * are used. This is probably not that helpful currently, we would have to the
   * tell the solver that these are axioms.
   *
   * The axioms are added to the last part of the list of formulas.
   *
   * @param f The list of formulas to scan for bitwise operations.
   */
  private void addBitwiseAxioms(List<BooleanFormula> f) {
    BooleanFormula bitwiseAxioms = bfmgr.makeTrue();

    for (BooleanFormula fm : f) {
      BooleanFormula a = fmgr.getBitwiseAxioms(fm);
      if (!bfmgr.isTrue(a)) {
        bitwiseAxioms =  fmgr.getBooleanFormulaManager().and(bitwiseAxioms, a);
      }
    }

    if (!bfmgr.isTrue(bitwiseAxioms)) {
      logger.log(Level.ALL, "DEBUG_3", "ADDING BITWISE AXIOMS TO THE",
          "LAST GROUP: ", bitwiseAxioms);
      int lastIndex = f.size()-1;
      f.set(lastIndex, bfmgr.and(f.get(lastIndex), bitwiseAxioms));
    }
  }

  /**
   * Try to find out which formulas out of a list of formulas are relevant for
   * making the conjunction unsatisfiable.
   * This method honors the {@link #direction} configuration option.
   *
   * @param f The list of formulas to check.
   * @return A sublist of f that contains the useful formulas.
   */
  private List<BooleanFormula> getUsefulBlocks(List<BooleanFormula> f) throws SolverException, InterruptedException {

    cexAnalysisGetUsefulBlocksTimer.start();

    // try to find a minimal-unsatisfiable-core of the trace (as Blast does)

    try (ProverEnvironment thmProver = solver.newProverEnvironment()) {

    logger.log(Level.ALL, "DEBUG_1", "Calling getUsefulBlocks on path",
            "of length:", f.size());

    final BooleanFormula[] needed = new BooleanFormula[f.size()];
    for (int i = 0; i < needed.length; ++i) {
      needed[i] =  bfmgr.makeTrue();
    }
    final boolean backwards = direction == CexTraceAnalysisDirection.BACKWARDS;
    final int start = backwards ? f.size()-1 : 0;
    final int increment = backwards ? -1 : 1;
    int toPop = 0;

    while (true) {
      boolean consistent = true;
      // 1. assert all the needed constraints
      for (BooleanFormula aNeeded : needed) {
        if (!bfmgr.isTrue(aNeeded)) {
          thmProver.push(aNeeded);
          ++toPop;
        }
      }
      // 2. if needed is inconsistent, then return it
      if (thmProver.isUnsat()) {
        f = Arrays.asList(needed);
        break;
      }
      // 3. otherwise, assert one block at a time, until we get an
      // inconsistency
      if (direction == CexTraceAnalysisDirection.ZIGZAG) {
        int s = 0;
        int e = f.size()-1;
        boolean fromStart = false;
        while (true) {
          int i = fromStart ? s++ : e--;
          fromStart = !fromStart;

          BooleanFormula t = f.get(i);
          thmProver.push(t);
          ++toPop;
          if (thmProver.isUnsat()) {
            // add this block to the needed ones, and repeat
            needed[i] = t;
            logger.log(Level.ALL, "DEBUG_1",
                "Found needed block: ", i, ", term: ", t);
            // pop all
            while (toPop > 0) {
              --toPop;
              thmProver.pop();
            }
            // and go to the next iteration of the while loop
            consistent = false;
            break;
          }

          if (e < s) {
            break;
          }
        }
      } else {
        for (int i = start;
             backwards ? i >= 0 : i < f.size();
             i += increment) {
          BooleanFormula t = f.get(i);
          thmProver.push(t);
          ++toPop;
          if (thmProver.isUnsat()) {
            // add this block to the needed ones, and repeat
            needed[i] = t;
            logger.log(Level.ALL, "DEBUG_1",
                "Found needed block: ", i, ", term: ", t);
            // pop all
            while (toPop > 0) {
              --toPop;
              thmProver.pop();
            }
            // and go to the next iteration of the while loop
            consistent = false;
            break;
          }
        }
      }
      if (consistent) {
        // if we get here, the trace is consistent:
        // this is a real counterexample!
        break;
      }
    }

    while (toPop > 0) {
      --toPop;
      thmProver.pop();
    }

    }

    logger.log(Level.ALL, "DEBUG_1", "Done getUsefulBlocks");

    cexAnalysisGetUsefulBlocksTimer.stop();

    return f;
  }

  /**
   * Put the list of formulas into the order in which they should be given to
   * the solver, as defined by the {@link #direction} configuration option.
   * @param traceFormulas The list of formulas to check.
   * @return The same list of formulas in different order,
   *         and each formula has its position in the original list as third element of the pair.
   */
  private List<Triple<BooleanFormula, AbstractState, Integer>> orderFormulas(
          final List<BooleanFormula> traceFormulas, final List<AbstractState> pAbstractionStates) {

    // In this list are all formulas together with their position in the original list
    ImmutableList<Triple<BooleanFormula, AbstractState, Integer>> result = direction.orderFormulas(traceFormulas,
                                                                                                   pAbstractionStates,
                                                                                                   variableClassification,
                                                                                                   loopStructure,
                                                                                                   fmgr);
    assert traceFormulas.size() == result.size();
    assert ImmutableMultiset.copyOf(from(result).transform(Triple::getFirst))
            .equals(ImmutableMultiset.copyOf(traceFormulas))
        : "Ordered list does not contain the same formulas with the same count";
    return result;
  }

  /**
   * Get the interpolants from the solver after the formulas have been proved
   * to be unsatisfiable.
   *
   * @param pInterpolator The references to the interpolation groups, sorting depends on the solver-stack.
   * @param formulasWithStatesAndGroupdIds list of (F,A,T) of path formulae F
   *        with their interpolation group I and the abstract state A,
   *        where a path formula F is the path before/until the abstract state A.
   *        The list is sorted in the "correct" order along the counterexample.
   * @return A list of (N-1) interpolants for N formulae.
   */
  private <T> List<BooleanFormula> getInterpolants(Interpolator<T> pInterpolator,
      List<Triple<BooleanFormula, AbstractState, T>> formulasWithStatesAndGroupdIds)
          throws SolverException, InterruptedException {
    // TODO replace with Config-Class-Constructor-Injection?
    final  ITPStrategy<T> itpStrategy;
    switch (strategy) {
      case SEQ_CPACHECKER:
        itpStrategy = new SequentialInterpolation<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      case SEQ:
        itpStrategy = new SequentialInterpolationWithSolver<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      case TREE_WELLSCOPED:
        itpStrategy = new WellScopedInterpolation<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      case TREE_NESTED:
        itpStrategy = new NestedInterpolation<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      case TREE_CPACHECKER:
        itpStrategy = new TreeInterpolation<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      case TREE:
        itpStrategy = new TreeInterpolationWithSolver<>(logger, shutdownNotifier, fmgr, bfmgr);
        break;
      default:
        throw new AssertionError("unknown interpolation strategy");
    }

    final List<BooleanFormula> interpolants = itpStrategy.getInterpolants(pInterpolator, formulasWithStatesAndGroupdIds);

    assert formulasWithStatesAndGroupdIds.size() - 1 == interpolants.size() : "we should return N-1 interpolants for N formulas.";

    if (verifyInterpolants) {
      itpStrategy.checkInterpolants(solver, formulasWithStatesAndGroupdIds, interpolants);
    }

    return interpolants;
  }

  /**
   * Get information about the error path from the solver after the formulas
   * have been proved to be satisfiable.
   *
   * @param f The list of formulas on the path.
   * @param pProver The solver.
   * @param elementsOnPath The ARGElements of the paths represented by f.
   * @return Information about the error path, including a satisfying assignment.
   */
  private CounterexampleTraceInfo getErrorPath(List<BooleanFormula> f,
      BasicProverEnvironment<?> pProver, Set<ARGState> elementsOnPath)
      throws CPATransferException, SolverException, InterruptedException {

    // get the branchingFormula
    // this formula contains predicates for all branches we took
    // this way we can figure out which branches make a feasible path
    BooleanFormula branchingFormula = pmgr.buildBranchingFormula(elementsOnPath);

    if (bfmgr.isTrue(branchingFormula)) {
      return CounterexampleTraceInfo.feasible(
          f, pProver.getModelAssignments(), ImmutableMap.<Integer, Boolean>of());
    }

    // add formula to solver environment
    pProver.push(branchingFormula);

    // need to ask solver for satisfiability again,
    // otherwise model doesn't contain new predicates
    boolean stillSatisfiable = !pProver.isUnsat();

    if (stillSatisfiable) {
      List<ValueAssignment> model = pProver.getModelAssignments();
      return CounterexampleTraceInfo.feasible(
          f, model, pmgr.getBranchingPredicateValuesFromModel(model));

    } else {
      // this should not happen
      logger.log(Level.WARNING, "Could not get precise error path information because of inconsistent reachingPathsFormula!");

      dumpInterpolationProblem(f);
      dumpFormulaToFile("formula", branchingFormula, f.size());

      return CounterexampleTraceInfo.feasible(
          f, ImmutableList.<ValueAssignment>of(), ImmutableMap.<Integer, Boolean>of());
    }
  }


  /**
   * Helper method to dump a list of formulas to files.
   */
  private void dumpInterpolationProblem(List<BooleanFormula> f) {
    int k = 0;
    for (BooleanFormula formula : f) {
      dumpFormulaToFile("formula", formula, k++);
    }
  }

  private void dumpFormulaToFile(String name, BooleanFormula f, int i) {
    Path dumpFile = formatFormulaOutputFile(name, i);
    fmgr.dumpFormulaToFile(f, dumpFile);
  }

  private Path formatFormulaOutputFile(String formula, int index) {
    return fmgr.formatFormulaOutputFile("interpolation", cexAnalysisTimer.getNumberOfIntervals(), formula, index);
  }

  /**
   * This class encapsulates the used SMT solver for interpolation,
   * and keeps track of the formulas that are currently on the solver stack.
   *
   * An instance of this class can be used for several interpolation queries
   * in a row, and it will try to keep as many formulas as possible in the
   * SMT solver between those queries (so that the solver may reuse information
   * from previous queries, and hopefully might even return similar interpolants).
   *
   * When an instance won't be used anymore, call {@link #close()}.
   *
   */
  public class Interpolator<T> {

    public InterpolatingProverEnvironment<T> itpProver;
    private final List<Triple<BooleanFormula, AbstractState, T>> currentlyAssertedFormulas = new ArrayList<>();

    Interpolator() {
      itpProver = newEnvironment();
    }

    @SuppressWarnings("unchecked")
    public InterpolatingProverEnvironment<T> newEnvironment() {
      // This is safe because we don't actually care about the value of T,
      // only the InterpolatingProverEnvironment itself cares about it.
      return (InterpolatingProverEnvironment<T>)solver.newProverEnvironmentWithInterpolation();
    }

    /**
     * Counterexample analysis and predicate discovery.
     * @param f the formulas for the path
     * @param elementsOnPath the ARGElements on the path (may be empty if no branching information is required)
     * @return counterexample info with predicated information
     */
    private CounterexampleTraceInfo buildCounterexampleTrace(
        List<BooleanFormula> f,
        List<AbstractState> pAbstractionStates,
        Set<ARGState> elementsOnPath,
        boolean computeInterpolants)
        throws SolverException, CPATransferException, InterruptedException {

      // Check feasibility of counterexample
      shutdownNotifier.shutdownIfNecessary();
      logger.log(Level.FINEST, "Checking feasibility of counterexample trace");
      satCheckTimer.start();

      boolean spurious;

      /* we use two lists, that contain identical formulas
       * with different additional information and (maybe) in different order:
       * 1) formulasWithStatesAndGroupdIds contains elements (F,A,T)
       *      with a path formula F that represents the path until the abstract state A and has the ITP-group T.
       *      It is sorted 'forwards' along the counterexample and is the basis for getting interpolants.
       * 2) orderedFormulas contains elements (F,A,I)
       *      with a path formula F that represents the path until the abstract state A.
       *      It is sorted depending on the {@link CexTraceAnalysisDirection} and
       *      is only used to check the counterexample for satisfiability.
       *      Depending on different directions, different interpolants
       *      might be computed from the solver's proof for unsatisfiability.
       */
      List<Triple<BooleanFormula, AbstractState, T>> formulasWithStatesAndGroupdIds;
      List<Triple<BooleanFormula, AbstractState, Integer>> orderedFormulas;

      if (pAbstractionStates.isEmpty()) {
        pAbstractionStates = new ArrayList<>(Collections.<AbstractState>nCopies(f.size(), null));
      }
      assert pAbstractionStates.size() == f.size() : "each pathFormula must end with an abstract State";

      try {

        if (getUsefulBlocks) {
          f = Collections.unmodifiableList(getUsefulBlocks(f));
        }

        if (dumpInterpolationProblems) {
          dumpInterpolationProblem(f);
        }

        // re-order formulas if needed
        orderedFormulas = orderFormulas(f, pAbstractionStates);
        assert orderedFormulas.size() == f.size();

        // initialize all interpolation group ids with "null"
        formulasWithStatesAndGroupdIds = new ArrayList<>(Collections.<Triple<BooleanFormula, AbstractState, T>>nCopies(f.size(), null));

        // ask solver for satisfiability
        spurious = checkInfeasabilityOfTrace(orderedFormulas, formulasWithStatesAndGroupdIds);
        assert formulasWithStatesAndGroupdIds.size() == f.size();
        assert !formulasWithStatesAndGroupdIds.contains(null); // has to be filled completely
        if(!spurious){
//          ImmutableList<ValueAssignment> myAssig = itpProver.getModelAssignments();
//          for(ValueAssignment v:myAssig){
//            String s = v.getName();
//            System.out.println(v);
//          }
//          System.out.println("************************");
        }
      } finally {
        satCheckTimer.stop();
      }

      logger.log(Level.FINEST, "Counterexample trace is", (spurious ? "infeasible" : "feasible"));


      // Get either interpolants or error path information
      CounterexampleTraceInfo info;
      if (spurious) {

        if (computeInterpolants) {
          SymInfo.lastFalse = -1;
          final List<BooleanFormula> interpolants = getInterpolants(this, formulasWithStatesAndGroupdIds);
          if (logger.wouldBeLogged(Level.ALL)) {
            int i = 1;
            for (BooleanFormula itp : interpolants) {
              logger.log(Level.ALL, "For step", i++, "got:", "interpolant", itp);
            }
          }

          info = CounterexampleTraceInfo.infeasible(interpolants);
        } else {
          info = CounterexampleTraceInfo.infeasibleNoItp();
        }

      } else {
     // this is a real bug
        info = getErrorPath(f, itpProver, elementsOnPath);
        for(AbstractState ps:pAbstractionStates){
          ((ARGState)ps).setDonotCover(true);
        }
        ArrayList<T> itpGroupsIds1 = new ArrayList<>(Collections.<T> nCopies(f.size(), null));
        try {
          allResult(f, pAbstractionStates,itpGroupsIds1);
        } catch (InvalidConfigurationException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        } catch (IOException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        } catch (ParserException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }

      }

      logger.log(Level.ALL, "Counterexample information:", info);

      return info;
    }

    private void allResult(List<BooleanFormula> pF, List<AbstractState> pa, List<T> itpGroupsIds)
            throws UnrecognizedCCodeException, UnrecognizedCFAEdgeException, InterruptedException, InvalidConfigurationException, IOException, ParserException {
      // TODO Auto-generated method stub
      int pASize = pa.size();
      int pFSize = pF.size();
      itpProver.close();
      currentlyAssertedFormulas.clear();
      itpProver = newEnvironment();
      SSAMap ssa = PredicateAbstractState.getPredicateState(pa.get(pASize-1)).getAbstractionFormula().getBlockFormula().getSsa();
      StringBuilder sb = new StringBuilder();
      /*********can be changed*********/
      sb.append("double o[3];\r\n");
      sb.append("int main(){ int x;\r\n");
      sb.append(" if(o[0]>0){} if(o[1]>0){x=1;} if(o[2]>0){x=2;}");
      // if(o[3]>0){x=3;} if(o[4]>0){x=4;} if(o[5]>0){x=6;}
      sb.append("\r\n};");
      int length = 2 ;  // the length of the array test[2] in the verified program
      /*********end*********/
      CFA newCfa = MyInfo.parse(sb.toString(),"main");
      CFANode mainNode = newCfa.getMainFunction();
      CFANode tmpNode=mainNode;
      List<CFAEdge> outEdgesInit = tmpNode.getLeavingEdge();
      while(outEdgesInit.size()==1){
         tmpNode=outEdgesInit.get(0).getSuccessor();
         outEdgesInit = tmpNode.getLeavingEdge();
      }
      List<String> poss= new ArrayList<String>();
      File file = new File("allResults.txt");  // the file that save all possibles,like 000,001,...
      FileReader fr = new FileReader(file);
      BufferedReader br = new BufferedReader(fr);
      String brs = "";
      while((brs=br.readLine())!=null){
        poss.add(brs);
      }

      int ps=0;
      itpGroupsIds = new ArrayList<>(Collections.<T> nCopies(pF.size(),null));
      int index0 = 0;
      for (int j = 0; j < pFSize-1; j++) {
        BooleanFormula f = pF.get(j);
          T it = itpProver.push(f);
          itpGroupsIds.set(index0, it);
   //       tToFormula.put(it, f);
          index0++;
      }
      BooleanFormula tf=  pF.get(pFSize-1);
      do{
        System.out.println("****************");
        itpProver.close();
        currentlyAssertedFormulas.clear();
        itpProver = newEnvironment();
         index0 = 0;
        for (int j = 0; j < pFSize-1; j++) {
          BooleanFormula f = pF.get(j);
            T it = itpProver.push(f);
            itpGroupsIds.set(index0, it);
            index0++;
        }
      List<CFAEdge> outEdges=outEdgesInit;
      BooleanFormula nf = bfmgr.makeTrue();
      String s="";
      if(ps<poss.size()){
        s=poss.get(ps);
        ps++;
      }
      else{
        break;
      }
      int ithEdge=0;
      while(outEdges.size()!=0){
        if(outEdges.size()==1){
          CFAEdge edge =outEdges.get(0);
          CFANode node = edge.getSuccessor();
          outEdges = node.getLeavingEdge();
          continue;
        }
      CFAEdge edge =outEdges.get(0);

      char ch= s.charAt(ithEdge);
      ithEdge++;

      if(edge instanceof CAssumeEdge){
        if(ch=='0'){
          if(((CAssumeEdge) edge).getTruthAssumption()){
            edge=outEdges.get(1);
          }
        }
        else{
          if(!((CAssumeEdge) edge).getTruthAssumption()){
            edge=outEdges.get(1);
          }
        }
        System.out.println(edge);
        PointerTargetSetBuilder pts = MyInfo.converter.createPointerTargetSetBuilder(MyInfo.lastOldFormula.getPointerTargetSet());
        ErrorConditions errorConditions = new ErrorConditions(bfmgr);
        Constraints constraints = new Constraints(bfmgr);
        BooleanFormula newEdge = MyInfo.converter.createFormulaForEdge(edge, "main", ssa.builder(), pts, constraints, errorConditions);
        nf = fmgr.makeAnd(nf, newEdge);
        CFANode node = edge.getSuccessor();
        outEdges = node.getLeavingEdge();
      }

      }
      BooleanFormula ttf= fmgr.makeAnd(tf, nf);
      T it = itpProver.push(ttf);
      itpGroupsIds.set(index0, it);





      try {
        if(!itpProver.isUnsat()){
          Model model = itpProver.getModel();
          //System.out.println(model);
          ImmutableList<ValueAssignment> values = itpProver.getModelAssignments();

          int value=-1;
          List<Integer> allAddresses = new ArrayList<Integer>();
          Map<Integer,List<Pair<Integer,String>>> finalResult = new HashMap<Integer,List<Pair<Integer,String>>>(2);
          for(ValueAssignment v : values){
            //System.out.println(v);
            String key =v.toString();
            if(key.contains("__ADDRESS_OF_main::test:")){
              //System.out.println("address_of_o="+key);
              value = Integer.parseInt(v.getValue().toString());
              for(int i=0;i<length;i++){
                allAddresses.add(value+i*64);
              }
              break;
            }
          }
          for(ValueAssignment v : values){
            //System.out.println(v);
            String key =v.toString();
//            if(key.contains("__ADDRESS_OF_o:")){
//              //System.out.println("address_of_o="+key);
//              value = Integer.parseInt(v.getValue().toString());
//              for(int i=0;i<length;i++){
//                allAddresses.add(value+i*64);
//              }
//            }
            if(key.startsWith("*double@")&&allAddresses.size()!=0){
              int index = Integer.parseInt(key.substring(key.indexOf("@")+1,key.indexOf("(")));
              int curAddr = Integer.parseInt(key.substring(key.indexOf("(")+1,key.indexOf(")")));
              if(allAddresses.contains(curAddr)){
                if(finalResult.size()==0){
                  Pair<Integer,String> pair = Pair.of(curAddr, v.getValue().toString());
                  List<Pair<Integer,String>> list = new ArrayList<Pair<Integer,String>>();
                  list.add(pair);
                  finalResult.put(index, list);
                }
                else{
                   int hasIndex = finalResult.keySet().iterator().next();
                   if(hasIndex<index){
                     finalResult.clear();
                     Pair<Integer,String> pair = Pair.of(curAddr, v.getValue().toString());
                     List<Pair<Integer,String>> list = new ArrayList<Pair<Integer,String>>();
                     list.add(pair);
                     finalResult.put(index, list);
                   }
                   else if(hasIndex==index){
                     List<Pair<Integer,String>> list = finalResult.get(index);
                     Pair<Integer,String> pair = Pair.of(curAddr, v.getValue().toString());
                     list.add(pair);
                   }
                }
              }
            }
          }

          System.out.println(finalResult);
          itpProver.pop();
          itpGroupsIds.set(index0, null);


        }
      } catch (SolverException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      }while(true);

    }

    /**
     * Check the satisfiability of a list of formulas, using them in the given order.
     * This method honors the {@link #incrementalCheck} configuration option.
     * It also updates the SMT solver stack and the {@link #currentlyAssertedFormulas}
     * list that is used if {@link #reuseInterpolationEnvironment} is enabled.
     *
     * @param traceFormulas The list of formulas to check, each formula with its index of where it should be added in the list of interpolation groups.
     * @param formulasWithStatesAndGroupdIds The list where to store the references to the interpolation groups. This is just a list of 'identifiers' for the formulas.
     * @return True if the formulas are unsatisfiable.
     */
    private boolean checkInfeasabilityOfTrace(
        final List<Triple<BooleanFormula, AbstractState, Integer>> traceFormulas,
        final List<Triple<BooleanFormula, AbstractState, T>> formulasWithStatesAndGroupdIds)
            throws InterruptedException, SolverException {

      // first identify which formulas are already on the solver stack,
      // which formulas need to be removed from the solver stack,
      // and which formulas need to be added to the solver stack
      ListIterator<Triple<BooleanFormula, AbstractState, Integer>> todoIterator = traceFormulas.listIterator();
      ListIterator<Triple<BooleanFormula, AbstractState, T>> assertedIterator = currentlyAssertedFormulas.listIterator();

      int firstBadIndex = -1; // index of first mis-matching formula in both lists

      while (assertedIterator.hasNext()) {
        Triple<BooleanFormula, AbstractState, T> assertedFormula = assertedIterator.next();

        if (!todoIterator.hasNext()) {
          firstBadIndex = assertedIterator.previousIndex();
          break;
        }

        Triple<BooleanFormula, AbstractState, Integer> todoFormula = todoIterator.next();

        if (todoFormula.getFirst().equals(assertedFormula.getFirst())) {
          // formula is already in solver stack in correct location
          formulasWithStatesAndGroupdIds.set(todoFormula.getThird(), assertedFormula);

        } else {
          firstBadIndex = assertedIterator.previousIndex();
          // rewind iterator by one so that todoFormula will be added to stack
          todoIterator.previous();
          break;
        }
      }

      // now remove the formulas from the solver stack where necessary
      if (firstBadIndex == -1) {
        // solver stack was already empty, nothing do to

      } else if (firstBadIndex == 0) {
        // Create a new environment instead of cleaning up the old one
        // if no formulas need to be reused.
        itpProver.close();
        itpProver = newEnvironment();
        currentlyAssertedFormulas.clear();

      } else {
        assert firstBadIndex > 0;
        // list with all formulas on solver stack that we need to remove
        // (= remaining formulas in currentlyAssertedFormulas list)
        List<Triple<BooleanFormula, AbstractState, T>> toDeleteFormulas =
            currentlyAssertedFormulas.subList(firstBadIndex,
                                              currentlyAssertedFormulas.size());

        // remove formulas from solver stack
        for (int i = 0; i < toDeleteFormulas.size(); i++) {
          itpProver.pop();
        }
        toDeleteFormulas.clear(); // this removes from currentlyAssertedFormulas

        reusedFormulasOnSolverStack += currentlyAssertedFormulas.size();
      }

      boolean isStillFeasible = true;

      // we do only need this unsat call here if we are using the incremental
      // checking option, otherwise it is anyway done later on
      if (incrementalCheck && !currentlyAssertedFormulas.isEmpty()) {
        isStillFeasible = !itpProver.isUnsat();
      }

      // add remaining formulas to the solver stack
      while (todoIterator.hasNext()) {
        Triple<BooleanFormula, AbstractState, Integer> p = todoIterator.next();
        BooleanFormula f = p.getFirst();
        AbstractState state = p.getSecond();
        int index = p.getThird();

        assert formulasWithStatesAndGroupdIds.get(index) == null;
        T itpGroupId = itpProver.push(f);
        final Triple<BooleanFormula, AbstractState, T> assertedFormula = Triple.of(f, state, itpGroupId);
        formulasWithStatesAndGroupdIds.set(index, assertedFormula);
        currentlyAssertedFormulas.add(assertedFormula);


        // We need to iterate through the full loop
        // to add all formulas, but this prevents us from doing further sat checks.
        if (incrementalCheck && isStillFeasible && !bfmgr.isTrue(f)) {
          isStillFeasible = !itpProver.isUnsat();
        }
      }

      assert Iterables.elementsEqual(
          from(traceFormulas).transform(Triple::getFirst),
          from(currentlyAssertedFormulas).transform(Triple::getFirst));

      // we have to do the sat check every time, as it could be that also
      // with incremental checking it was missing (when the path is infeasible
      // and formulas get pushed afterwards)
      return itpProver.isUnsat();
    }

    private void close() {
      itpProver.close();
      itpProver = null;
      currentlyAssertedFormulas.clear();
    }

    private boolean SymbolicInterpolant1(List<BooleanFormula> pF,
        List<AbstractState> pa, List<T> itpGroupsIds)
        throws InterruptedException, SolverException {
      int fsize = pF.size();
      int x = 0;
      int braNum = 0; // count the number of branches
      int countBra = 0;
      boolean skip = false;
      Map<T,BooleanFormula> tToFormula=new HashMap<T,BooleanFormula>();
      List<Integer> indices = new ArrayList<Integer>();
      int n = 0;
      /* <num1,num2>:num1:the index of branches num2: the index of states */
      Map<Integer, Integer> map = new HashMap<Integer, Integer>();
      Set<Integer> pSId = new HashSet<Integer>();// the ID of states that
                            // pointed by an assume
                            // edge
                            // for (int i = 0; i <
                            // pa.size(); i++) {


      if (SymInfo.result != Result.FALSE) {
        for (int j = fsize - 1; j > 0; j--) {
          ARGState curState = (ARGState) pa.get(j);
          CFANode loc = curState.getLoc();
          loc = loc == null ? AbstractStates
              .extractLocation(curState) : loc;
          curState.setLoc(loc);
          x = x + 1;
          if (loc.getNumLeavingEdges() > 1
              && loc.getLeavingEdge(0) instanceof CAssumeEdge) {

            break;
          }
          // loc.setTrueFull(true);
          // loc.setErrorFull(true);
        }
      } else {
        x = 1;
      }
      // boolean end = false;
      ARGState stopState = null;
      // int tmpBraNum = braNum;
      // BooleanFormula fb = null;
      // int debugCount = 0;
      itpProver.close();
      currentlyAssertedFormulas.clear();
      itpProver = newEnvironment();
      // boolean isFirst = true;
      int lastFalse = SymInfo.lastFalse;
      int index0 = 0;
      // boolean firstIsLast=false;
      itpGroupsIds = new ArrayList<>(Collections.<T> nCopies(pF.size(),
          null));
      List<BooleanFormula> braFormulas = new ArrayList<BooleanFormula>();
      for (int j = 0; j < fsize; j++) {
        BooleanFormula f = pF.get(j);
        if (SymInfo.braIds.contains(j - 1) && j >= SymInfo.lastFalse) {
          braFormulas.add(f);
        } else /* if(!SymInfo.braIds.contains(j - 1)) */{
          T it = itpProver.push(f);
          itpGroupsIds.set(index0, it);
          tToFormula.put(it, f);
          index0++;
        }
        // else{
        // T it = itpProver.push(SymInfo.bfmr.makeBoolean(true));
        // itpGroupsIds.set(index0, it);
        // index0++;
        // }
      }
      lastFalse = index0;
      int bsize = braFormulas.size();
      for (int j = bsize - 1; j >= 0; j--) {
        BooleanFormula f = braFormulas.get(j);
        T it = itpProver.push(f);
        itpGroupsIds.set(index0, it);
        tToFormula.put(it, f);
        index0++;
      }
      itpProver.isUnsat();
      List<T> tmpItpIds1 = new ArrayList<T>();
      // int numth = 0;
      int want = 0;
      boolean over = false;
      boolean stop = false;
      // long time=System.currentTimeMillis();
      for (int i = lastFalse; i < fsize - 1 && !over; i++) {
        tmpItpIds1 = itpGroupsIds.subList(0, i);
        BooleanFormula intp = itpProver.getInterpolant(tmpItpIds1);
        if (intp.toString().equals("true")) {
          stop = true;
          break;
        } else if (!intp.toString().equals("false")) {
          for (int j = 2; fsize - j > i; j++) {
            intp = itpProver
                .getInterpolant(tmpItpIds1);
            if (intp.toString().equals("false")) {
              // System.out.println("j="+j);
              int tmp = fsize - j - lastFalse;
              int braSize = SymInfo.braIds.size();
              int unreachIndex = SymInfo.braIds.get(braSize - tmp
                  - 1);
              want = unreachIndex + 1;
              over = true;
              break;
            }
          }
        } else {
          // System.out.println("i="+i);
          int isize = itpGroupsIds.size();
          int tmp = isize - 1 - i;
          int k = 1;
          while (tmp > 0) {
            itpProver.pop();
            tmp--;
            itpGroupsIds.set(isize - k, null);
            k++;
          }
          if (itpProver.isUnsat()) {
            tmp = i - lastFalse;
            int braSize = SymInfo.braIds.size();
            int unreachIndex = SymInfo.braIds
                .get(braSize - tmp - 1);
            want = unreachIndex + 1;
            break;
          } else {
            stop = true;
            over = true;
          }
          fsize = itpGroupsIds.size();
        }
      }
      // time=System.currentTimeMillis()-time;
      // System.out.print(time+"**");
      if (stop) {
        return true;
      }
      if (want == 0) {
        want = SymInfo.lastFalse;
      }
      // System.out.println(pa.get(want));
      // if(want==pa.size()){
      // return true;
      // }
      stopState = (ARGState) pa.get(want);
      CFANode locStop = stopState.getLoc();
      int tmpWant = want;
      do {
        if (locStop.getNumLeavingEdges() > 1
            && locStop.getLeavingEdge(0) instanceof CAssumeEdge) {

          break;
        }
        tmpWant++;
        if (tmpWant >= fsize) {
          stopState = (ARGState) pa.get(want);
          break;
        }
        stopState = (ARGState) pa.get(tmpWant);
        locStop = stopState.getLoc();
      } while (true);
      boolean start = false, special = false;
      boolean oneBra = false;
      int idLS = 0; // the index of the last unreachable state
      boolean debug = false;
      // long time2 = System.currentTimeMillis();
      Set<T> specialRemove = new HashSet<T>();
      // time=System.currentTimeMillis();
      BooleanFormula curIntp = null;
      BooleanFormula other=SymInfo.bfmr.makeBoolean(true);
      if(x==1){
        x=3;
      }
      for (int j = fsize - (x - 1); j >= 1 && !oneBra; j--) {
        ARGState curState = (ARGState) pa.get(j);

        CompositeState curComp = (CompositeState) curState.getWrappedStates().get(0);
        List<AbstractState> curWrap = curComp.getWrappedStates();
        String curCallStack="";
        int curCountCallStack=-1;
        for(AbstractState abs: curWrap){
           if(abs instanceof CallstackState){
             curCallStack=((CallstackState) abs).getMyStack().toString();
             break;
           }
        }
        //if(SymInfo.callstack.keySet().contains(curCallStack)){
       //    curCountCallStack=SymInfo.callstack.get(curCallStack);
       // }
        CFANode loc = curState.getLoc();
        if (j == fsize) {
          BooleanFormula eitp = loc.getErrorIntp();
          if(eitp!=null&&!eitp.toString().equals("true")&&eitp.toString().equals("false")){
            other=fmgr.makeAnd(other,eitp);
          }

          continue;
        }
      //   System.out.println(j);
        if (debug) {
          break;
        }
        itpProver.close();
        currentlyAssertedFormulas.clear();
        itpProver = newEnvironment();

        // System.out.println("j=" + j);
        // T idFB = null;

        special = false;
        BooleanFormula tmpF = pF.get(j+1);
        tmpF=fmgr.uninstantiate(tmpF);
       // SymInfo.cePF.add(tmpF);
        if (curState != stopState && !start) {
          continue;
        } else if (curState == stopState) {
          start = true;
          special = true;
          idLS = j;
          debug=true;
        }


        if (loc == null) {
          loc = AbstractStates.extractLocation(curState);
          curState.setLoc(loc);
          if (loc.getTrueIntp() == null) {
            loc.setTrueIntp(SymInfo.bfmr.makeBoolean(false));
            curCountCallStack=SymInfo.countNumCallstack;
            SymInfo.callstack.put(curCallStack,curCountCallStack);
            SymInfo.countNumCallstack++;
            BooleanFormula f=SymInfo.bfmr.makeBoolean(true);
            loc.getErrIntp().put(curCountCallStack, f);
            loc.setErrorIntp(SymInfo.bfmr.makeBoolean(true));
            /**********/
            List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
            conj.add(f);
            Set<List<BooleanFormula>> disj=new HashSet<List<BooleanFormula>>();
            disj.add(conj);
            loc.getErrIntpForPrincess().put(curCountCallStack, disj);
            /**********/
          }
        }
        else{
          if(!SymInfo.callstack.containsKey(curCallStack)){
            curCountCallStack = SymInfo.countNumCallstack;
            SymInfo.callstack.put(curCallStack,curCountCallStack);
            SymInfo.countNumCallstack++;
            BooleanFormula f=SymInfo.bfmr.makeBoolean(true);
            loc.getErrIntp().put(curCountCallStack, f);
            /**********/
            List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
            conj.add(f);
            Set<List<BooleanFormula>> disj=new HashSet<List<BooleanFormula>>();
            disj.add(conj);
            loc.getErrIntpForPrincess().put(curCountCallStack, disj);
            /**********/
          }
          else{
            curCountCallStack=SymInfo.callstack.get(curCallStack);
            if(!loc.getErrIntp().keySet().contains(curCountCallStack)){
              BooleanFormula f=SymInfo.bfmr.makeBoolean(false);
              loc.getErrIntp().put(curCountCallStack, f);
              /**********/
              List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
              conj.add(f);
              Set<List<BooleanFormula>> disj=new HashSet<List<BooleanFormula>>();
              disj.add(conj);
              loc.getErrIntpForPrincess().put(curCountCallStack, disj);
              /**********/
            }
          }
        }
        if (!SymInfo.keyNode.contains(loc.getNodeNumber())) {
          if (!SymInfo.iskey(loc)) {
            loc.setEnd(true);
          }
          continue;
        }

        List<BooleanFormula> subPF = pF.subList(0, j + 1);
        List<Triple<BooleanFormula, AbstractState, Integer>> traceFormulas = orderFormulas(
            subPF, pa);
        itpGroupsIds = new ArrayList<>(Collections.<T> nCopies(j + 3,
            null));

        // itpProver.push(sucIntp);

        ListIterator<Triple<BooleanFormula, AbstractState, Integer>> todoIterator = traceFormulas
            .listIterator();
        ListIterator<Triple<BooleanFormula, AbstractState, T>> assertedIterator = currentlyAssertedFormulas
            .listIterator();

        int firstBadIndex = -1; // index of first mis-matching
                    // formula in both lists

        while (assertedIterator.hasNext()) {
          Triple<BooleanFormula, AbstractState, T> assertedFormula = assertedIterator
              .next();

          if (!todoIterator.hasNext()) {
            firstBadIndex = assertedIterator.previousIndex();
            break;
          }

          Triple<BooleanFormula, AbstractState, Integer> todoFormula = todoIterator
              .next();

          if (todoFormula.getFirst().equals(
              assertedFormula.getFirst())) {
            // formula is already in solver stack in correct
            // location
            @SuppressWarnings("unchecked")
            T itpGroupId = assertedFormula.getThird();
            itpGroupsIds
                .set(todoFormula.getThird() + 2, itpGroupId);
            tToFormula.put(itpGroupId, assertedFormula.getFirst());

          } else {
            firstBadIndex = assertedIterator.previousIndex();
            // rewind iterator by one so that todoFormula will
            // be added to stack
            todoIterator.previous();
            break;
          }
        }

        // now remove the formulas from the solver stack where
        // necessary
        if (firstBadIndex == -1) {
          // solver stack was already empty, nothing do to

        } else if (firstBadIndex == 0) {
          // Create a new environment instead of cleaning up the
          // old one
          // if no formulas need to be reused.
          itpProver.close();
          itpProver = newEnvironment();
          currentlyAssertedFormulas.clear();

        } else {
          assert firstBadIndex > 0;
          // list with all formulas on solver stack that we need
          // to remove
          // (= remaining formulas in currentlyAssertedFormulas
          // list)
          List<Triple<BooleanFormula, AbstractState, T>> toDeleteFormulas = currentlyAssertedFormulas
              .subList(firstBadIndex,
                  currentlyAssertedFormulas.size());

          // remove formulas from solver stack
          for (int i = 0; i < toDeleteFormulas.size(); i++) {
            itpProver.pop();
          }
          toDeleteFormulas.clear(); // this removes from
                        // currentlyAssertedFormulas

          reusedFormulasOnSolverStack += currentlyAssertedFormulas
              .size();
        }

        boolean isStillFeasible = true;

        if (incrementalCheck && !currentlyAssertedFormulas.isEmpty()) {
          if (itpProver.isUnsat()) {
            isStillFeasible = false;
          }
        }

        // add remaining formulas to the solver stack
        while (todoIterator.hasNext()) {
          Triple<BooleanFormula, AbstractState, Integer> p = todoIterator
              .next();
          BooleanFormula f = p.getFirst();
          AbstractState state = p.getSecond();
          int index = p.getThird();
          // if (special) {
          if (pSId.contains(((ARGState) state).getStateId())) {
            assert itpGroupsIds.get(index+2) == null;
            BooleanFormula tf = SymInfo.bfmr.makeBoolean(true);
            T itpGroupId = itpProver.push(tf);
            specialRemove.add(itpGroupId);
            itpGroupsIds.set(index + 2, itpGroupId);
            tToFormula.put(itpGroupId, tf);
          } else {
            assert itpGroupsIds.get(index+2) == null;
            T itpGroupId = itpProver.push(f);
            itpGroupsIds.set(index + 2, itpGroupId);
            tToFormula.put(itpGroupId, f);
          }
          // } else {
          /* original code */
          // if (pSId.contains(((ARGState) state).getStateId())) {
          // assert itpGroupsIds.get(index) == null;
          // T itpGroupId = itpProver.push(SymInfo.bfmr
          // .makeBoolean(true));
          // itpGroupsIds.set(index + 2, itpGroupId);
          // } else {
          // assert itpGroupsIds.get(index) == null;
          // T itpGroupId = itpProver.push(f);
          // itpGroupsIds.set(index + 2, itpGroupId);
          // }
          // }
          if (incrementalCheck && isStillFeasible && !bfmgr.isTrue(f)) {
            if (itpProver.isUnsat()) {
              // We need to iterate through the full loop
              // to add all formulas, but this prevents us
              // from doing further sat checks.
              isStillFeasible = false;
            }
          }
        }
        if (j == fsize - x) {
          //j=j-1;
          if (SymInfo.result != Result.FALSE) {
            CFANode nextLoc = AbstractStates.extractLocation(pa
                .get(j + 1));
            CAssumeEdge edge = (CAssumeEdge) loc.getEdgeTo(nextLoc);
            String opr = ((CBinaryExpression) edge.getExpression())
                .getOperator().toString();
            Object op1 = ((CBinaryExpression) edge.getExpression())
                .getOperand1();
            Object op2 = ((CBinaryExpression) edge.getExpression())
                .getOperand2();
            String lOrR = "N";
            if (op1 instanceof CLiteralExpression) {
              lOrR = "R";
            } else if (op2 instanceof CLiteralExpression) {
              lOrR = "L";
            } else {
              List<String> lv = new ArrayList<String>(4);
              edge.getExpression().getAllLVars(lv);
              lv.add(";");
              edge.getExpression().getAllRVars(lv);
              loc.addConds(lv);
            }
            Boolean truth = edge.getTruthAssumption();
            ARGState sucState = (ARGState) pa.get(j + 1);
            CompositeState sucComp = (CompositeState) sucState.getWrappedStates().get(0);
            List<AbstractState> sucWrap = curComp.getWrappedStates();
            String sucCallStack="";
            //int sucCountCallStack=-1;
            for(AbstractState abs: sucWrap){
               if(abs instanceof CallstackState){
                 sucCallStack=((CallstackState) abs).getMyStack().toString();
                 break;
               }
            }
            BooleanFormula errorIntp = pF.get(j + 1);
            errorIntp = fmgr.uninstantiate(errorIntp);
            // loc.getErrorIntps().add(errorIntp);
            loc.getOprs().add(Pair.of(truth, lOrR + "+" + opr));
            debug = true;
            if (errorIntp.toString().matches(".*\\*.*")) {
              stop = true;
              break;
            }
            if(!other.toString().equals("true")){
              errorIntp=fmgr.makeAnd(errorIntp, other);
            }
            errorIntp=makeNewERRORIntp(errorIntp,nextLoc,j,idLS,pa,sucCallStack);
            Map<Integer, BooleanFormula> errIntp = loc.getErrIntp();
            Map<Integer, Set<List<BooleanFormula>>> errorIntpForPrincess = loc.getErrIntpForPrincess();
            if(!SymInfo.callstack.keySet().contains(curCallStack)){
              curCountCallStack=SymInfo.countNumCallstack;
              SymInfo.callstack.put(curCallStack,curCountCallStack);
              SymInfo.countNumCallstack++;
            }
            else{
              curCountCallStack=SymInfo.callstack.get(curCallStack);
            }
            if(errIntp==null){
              errIntp=new HashMap<Integer, BooleanFormula>();
              //curCountCallStack=SymInfo.countNumCallstack;
              errIntp.put(curCountCallStack, errorIntp);
              loc.setErrIntp(errIntp);
              /**********/
              errorIntpForPrincess=loc.getErrIntpForPrincess();
              List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
              conj.add(errorIntp);
              Set<List<BooleanFormula>> disj=new HashSet<List<BooleanFormula>>();
              disj.add(conj);
              loc.getErrIntpForPrincess().put(curCountCallStack, disj);
              /**********/
            }
            else{
              if(errIntp.keySet().contains(curCountCallStack)){
                BooleanFormula bf=errIntp.get(curCountCallStack);
                bf=fmgr.makeOr(bf,errorIntp);
                errIntp.put(curCountCallStack, bf);
              }
              else{
                errIntp.put(curCountCallStack, errorIntp);
              }
              /**********/
              if(errorIntpForPrincess.keySet().contains(curCountCallStack)){
                Set<List<BooleanFormula>> disj = errorIntpForPrincess.get(curCountCallStack);
                List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
                conj.add(errorIntp);
                disj.add(conj);
              }
              else{
                Set<List<BooleanFormula>> disj = new HashSet<List<BooleanFormula>>();
                List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
                conj.add(errorIntp);
                disj.add(conj);
                loc.getErrIntpForPrincess().put(curCountCallStack, disj);
              }
              /**********/
            }
          }

        } else /* if (j < fsize - x) */
        {
          CFANode nextLoc;
          BooleanFormula errorIntp;
          BooleanFormula sucIntp;
          BooleanFormula intp1;
          nextLoc = ((ARGState) pa.get(j + 1)).getLoc();
          errorIntp = loc.getErrorIntp();
          sucIntp = nextLoc.getErrorIntp();
          // if (edge instanceof CAssumeEdge) {
          // BooleanFormula ff = pF.get(j + 1);
          // if (ff.toString().matches(".*\\*.*")) {
          // break;
          // }
          // ff = fmgr.uninstantiate(ff);
          // BooleanFormula curErr = fmgr.makeAnd(ff, sucIntp);
          // errorIntp = fmgr.makeOr(errorIntp, curErr);
          // loc.setErrorIntp(errorIntp);
          // continue;
          // }
          BooleanFormula pj = null; // pj represents the formulas from
                        // sj to se, se is the error
                        // state
          if (special) {
            for (int k = j + 1; k < fsize; k++) {
              BooleanFormula tp = pF.get(k);
              if (pj == null) {
                pj = pF.get(k);
              } else {
                // if(indices.contains(k)){
                // tp=fmgr.makeNot(tp);
                // }
                pj = fmgr.makeAnd(pj, tp);
              }
            }
          } else {
            pj = pF.get(j + 1);
          }
          if (j == fsize - x + 1) {
            errorIntp = SymInfo.bfmr.makeBoolean(true); //
            Map<Integer, BooleanFormula> errIntp = loc.getErrIntp();
            Map<Integer, Set<List<BooleanFormula>>> errorIntpForPrincess = loc.getErrIntpForPrincess();
            if(!SymInfo.callstack.keySet().contains(curCallStack)){
              curCountCallStack=SymInfo.countNumCallstack;
              SymInfo.callstack.put(curCallStack,curCountCallStack);
              SymInfo.countNumCallstack++;
            }
            else{
              curCountCallStack=SymInfo.callstack.get(curCallStack);
            }
            if(errIntp==null){
              errIntp=new HashMap<Integer, BooleanFormula>();
             // curCountCallStack=SymInfo.countNumCallstack;
              errIntp.put(curCountCallStack, errorIntp);
              loc.setErrIntp(errIntp);
              /**********/
              errorIntpForPrincess=loc.getErrIntpForPrincess();
              List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
              conj.add(errorIntp);
              Set<List<BooleanFormula>> disj=new HashSet<List<BooleanFormula>>();
              disj.add(conj);
              loc.getErrIntpForPrincess().put(curCountCallStack, disj);
              /**********/
            }
            else{
              if(errIntp.keySet().contains(curCountCallStack)){
                BooleanFormula bf=errIntp.get(curCountCallStack);
                bf=fmgr.makeAnd(bf,errorIntp);
                errIntp.put(curCountCallStack, bf);
              }
              else{
                errIntp.put(curCountCallStack, errorIntp);
              }
              /**********/
              if(errorIntpForPrincess.keySet().contains(curCountCallStack)){
                Set<List<BooleanFormula>> disj = errorIntpForPrincess.get(curCountCallStack);
                List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
                conj.add(errorIntp);
                disj.add(conj);
              }
              else{
                Set<List<BooleanFormula>> disj = new HashSet<List<BooleanFormula>>();
                List<BooleanFormula> conj=new ArrayList<BooleanFormula>();
                conj.add(errorIntp);
                disj.add(conj);
                loc.getErrIntpForPrincess().put(curCountCallStack, disj);
              }
              /**********/
            }
           // loc.setErrorIntp(errorIntp);
            debug = true;
            continue;
          }
          // if (pj.toString().equals("true")) {
          // errorIntp = fmgr.makeOr(errorIntp, sucIntp);
          // errorIntp = fmgr.uninstantiate(errorIntp);
          // loc.setErrorIntp(errorIntp);
          // continue;
          // }

          T itpGroupId0 = itpProver.push(pj);
          itpGroupsIds.set(0, itpGroupId0); //

          BooleanFormula tsucIntp;
          SSAMap ssa = PredicateAbstractState
              .getPredicateState(pa.get(j + 1))
              .getAbstractionFormula().getBlockFormula().getSsa();
          if (special) {
            /*
             * starting with s(j+1), The formula of each assume edge
             * is negated
             */

            tsucIntp = SymInfo.bfmr.makeBoolean(true);
            for (int k = j + 1; k < fsize; k++) {
              BooleanFormula tp = pF.get(k);
              if (indices.contains(k)) {
                tp = fmgr.makeNot(tp);
                tsucIntp = fmgr.makeAnd(tsucIntp, tp);
              }

            }
            tsucIntp = fmgr.instantiate(tsucIntp, ssa);
          } else {
            // SSAMap ssa = PredicateAbstractState
            // .getPredicateState(pa.get(j))
            // .getAbstractionFormula().getBlockFormula()
            // .getSsa();
            tsucIntp = fmgr.instantiate(sucIntp, ssa);
          }
          T itpGroupId1 = itpProver.push(tsucIntp);
          itpGroupsIds.set(1, itpGroupId1);
          tToFormula.put(itpGroupId1, tsucIntp);
          if (!itpProver.isUnsat()) {
            break;
          }
          // if (special) {
          // List<T> termB=itpGroupsIds.subList(1, j + 3);
          // int tbsize=termB.size();
          // List<T> tmp=new ArrayList<T>();
          // for(int k=0;k<tbsize;k++){
          // T ith=termB.get(k);
          // if(!specialRemove.contains(ith)){
          // tmp.add(ith);
          // }
          // }
          // intp1 = itpProver.getInterpolant1(
          // itpGroupsIds.subList(0, 1),
          // tmp);
          // String funcname=loc.getFunctionName();
          // if(intp1.toString().contains("::")&&!intp1.toString().contains(funcname)){
          // stop=true;
          // break;
          // }
          // debug = true;
          // itpProver.pop();
          // itpProver.pop();
          // } else {
          intp1 = itpProver.getInterpolant(
              itpGroupsIds.subList(0, 2));
          // }
          if (intp1.toString().equals("false")
              || intp1.toString().equals("true")) {
            stop = true;
            break;
          }
          if (intp1.toString().matches(".*\\*.*")) {
            errorIntp = SymInfo.bfmr.makeBoolean(false);
            stop = true;
            break;
          } else {

            if (errorIntp.toString().equals("false")) {
              errorIntp = intp1;
            } else {
              errorIntp = fmgr.makeOr(errorIntp, intp1);
            }
            errorIntp = fmgr.uninstantiate(errorIntp);
            if (curIntp == null) {
              curIntp = errorIntp;
            }
            String sucCallStack="";
            ARGState sucState = (ARGState) pa.get(j + 1);
            CompositeState sucComp = (CompositeState) sucState.getWrappedStates().get(0);
            List<AbstractState> sucWrap = curComp.getWrappedStates();
            int sucCountCallStack=-1;
            for(AbstractState abs: sucWrap){
               if(abs instanceof CallstackState){
                 sucCallStack=((CallstackState) abs).getMyStack().toString();
                 break;
               }
            }
            errorIntp=makeNewERRORIntp(errorIntp,nextLoc,j,idLS,pa,sucCallStack);
          }
          /*
           * modify the call process of SMT solver
           */
          // {
          // int itpSize=itpGroupsIds.size();
          // T itpJ2 = itpGroupsIds.get(j+2);
          // itpGroupsIds.set(0,itpJ2);
          // itpGroupsIds.remove(j+2);
          // }
          Map<Integer, BooleanFormula> errIntp = loc.getErrIntp();
          if(!SymInfo.callstack.keySet().contains(curCallStack)){
            curCountCallStack=SymInfo.countNumCallstack;
            SymInfo.callstack.put(curCallStack,curCountCallStack);
            SymInfo.countNumCallstack++;
          }
          else{
            curCountCallStack=SymInfo.callstack.get(curCallStack);
          }
          if(errIntp==null){
            errIntp=new HashMap<Integer, BooleanFormula>();
           // curCountCallStack=SymInfo.countNumCallstack;
            errIntp.put(curCountCallStack, errorIntp);
            loc.setErrIntp(errIntp);

          }
          else{
            if(errIntp.keySet().contains(curCountCallStack)){
              BooleanFormula bf=errIntp.get(curCountCallStack);
              if(bf.toString().equals("false")||bf.toString().equals("true")){
                bf=errorIntp;
              }
              else{
                bf=fmgr.makeOr(bf,errorIntp);
              }
              errIntp.put(curCountCallStack, bf);
            }
            else{
              errIntp.put(curCountCallStack, errorIntp);
            }
          }
          loc.setErrorIntp(errorIntp);

        }

      }
      // time=System.currentTimeMillis()-time;
      // System.out.print(time+"&&");
      if (stop) {
        return true;
      }
      // System.out.println("time2=" + (System.currentTimeMillis() -
      // time2));
      /*
       * date: 2017.2.6 author: duan zhao function: optimize the code
       */
      oneBra = false;

      int itpSize = itpGroupsIds.size();
      // time = System.currentTimeMillis();
      for (int j = idLS - 1; j >= 1 && !oneBra; j--) {
        // System.out.println(j);
        ARGState curState = (ARGState) pa.get(j);
        CompositeState curComp = (CompositeState) curState.getWrappedStates().get(0);
        List<AbstractState> curWrap = curComp.getWrappedStates();
        String curCallStack="";
        int curCountCallStack=-1;
        for(AbstractState abs: curWrap){
           if(abs instanceof CallstackState){
             curCallStack=((CallstackState) abs).getMyStack().toString();
             break;
           }
        }
        CFANode loc = curState.getLoc();
        BooleanFormula tmpF = pF.get(j+1);
        tmpF=fmgr.uninstantiate(tmpF);
        //SymInfo.cePF.add(tmpF);
        if (loc == null) {
          loc = AbstractStates.extractLocation(curState);
          curState.setLoc(loc);
          if (loc.getTrueIntp() == null) {
            loc.setTrueIntp(SymInfo.bfmr.makeBoolean(false));
             curCountCallStack = SymInfo.countNumCallstack;
            SymInfo.callstack.put(curCallStack,curCountCallStack);
            SymInfo.countNumCallstack++;
            BooleanFormula f=SymInfo.bfmr.makeBoolean(true);
            loc.getErrIntp().put(curCountCallStack, f);
            //loc.setTrueIntp(SymInfo.bfmr.makeBoolean(false));
            loc.setErrorIntp(f);
          }
        }
        else{
          if(!SymInfo.callstack.containsKey(curCallStack)){
            curCountCallStack = SymInfo.countNumCallstack;
            SymInfo.callstack.put(curCallStack,curCountCallStack);
            SymInfo.countNumCallstack++;
            BooleanFormula f=SymInfo.bfmr.makeBoolean(false);
            loc.getErrIntp().put(curCountCallStack, f);
          }
          else{
            curCountCallStack=SymInfo.callstack.get(curCallStack);
            if(!loc.getErrIntp().keySet().contains(curCountCallStack)){
              BooleanFormula f=SymInfo.bfmr.makeBoolean(false);
              loc.getErrIntp().put(curCountCallStack, f);
            }
          }
        }
        if (!SymInfo.keyNode.contains(loc.getNodeNumber())) {
          if (!SymInfo.iskey(loc)) {
            loc.setEnd(true);
          }
          continue;
        }
        {
          CFANode nextLoc;
          BooleanFormula errorIntp;
          BooleanFormula sucIntp;
          BooleanFormula intp1=null;
          Map<Integer, BooleanFormula> errIntp = loc.getErrIntp();
          errorIntp = errIntp.get(curCountCallStack);

          String sucCallStack="";
          ARGState sucState = (ARGState) pa.get(j + 1);
          nextLoc = sucState.getLoc();
          //sucIntp = nextLoc.getErrorIntp();
          CompositeState sucComp = (CompositeState) sucState.getWrappedStates().get(0);
          List<AbstractState> sucWrap = sucComp.getWrappedStates();
          int sucCountCallStack=-1;
          for(AbstractState abs: sucWrap){
             if(abs instanceof CallstackState){
               sucCallStack=((CallstackState) abs).getMyStack().toString();
               break;
             }
          }
          sucCountCallStack=SymInfo.callstack.get(sucCallStack);
          sucIntp=nextLoc.getErrIntp().get(sucCountCallStack);
          if(sucIntp==null){

          }
          //CFAEdge curToSucEdge = loc.getEdgeTo(nextLoc);
          // if (curToSucEdge instanceof CAssumeEdge) {
          // BooleanFormula ff = pF.get(j + 1);
          // if (ff.toString().matches(".*\\*.*")) {
          // break;
          // }
          // ff = fmgr.uninstantiate(ff);
          // BooleanFormula curErr = fmgr.makeAnd(ff, sucIntp);
          // errorIntp = fmgr.makeOr(errorIntp, curErr);
          // loc.setErrorIntp(errorIntp);
          // itpGroupsIds.remove(itpSize - 1);
          // itpSize--;
          // itpProver.pop();
          // loc.seteIsEqSuc(false);
          // loc.setEc(true);
          // continue;
          // }
          BooleanFormula pj = null;
          pj = pF.get(j + 1);

          if (pj.toString().equals("true")) {
            errorIntp = fmgr.makeOr(errorIntp, sucIntp);
            errorIntp = fmgr.uninstantiate(errorIntp);
            errorIntp=makeNewERRORIntp(errorIntp,nextLoc,j,idLS,pa,sucCallStack);
            //int curCountCallStack=-1;
            if(!SymInfo.callstack.keySet().contains(curCallStack)){
              curCountCallStack=SymInfo.countNumCallstack;
              SymInfo.callstack.put(curCallStack,curCountCallStack);
              SymInfo.countNumCallstack++;
            }
            else{
              curCountCallStack=SymInfo.callstack.get(curCallStack);
            }

//            if(errIntp==null){
//              errIntp=new HashMap<Integer, BooleanFormula>();
//             // curCountCallStack=SymInfo.countNumCallstack;
//              errIntp.put(curCountCallStack, errorIntp);
//              loc.setErrIntp(errIntp);
//            }
//            else{
              //if(errIntp.keySet().contains(curCountCallStack)){
              //  BooleanFormula bf=errIntp.get(curCountCallStack);
              //  bf=fmgr.makeOr(bf,errorIntp);
              //  errIntp.put(curCountCallStack, bf);
              //}
              //else{
                errIntp.put(curCountCallStack, errorIntp);
              //}
           // }
            loc.setErrorIntp(errorIntp);
            itpGroupsIds.remove(itpSize - 1);
            itpSize--;
            itpProver.pop();
            if (errorIntp.toString().equals(sucIntp.toString())) {
              loc.seteIsEqSuc(true);
            } else {
              loc.seteIsEqSuc(false);
            }
//            int curCountCallStack=-1;
//            if(!SymInfo.callstack.keySet().contains(curCallStack)){
//              curCountCallStack=SymInfo.countNumCallstack;
//              SymInfo.callstack.put(curCallStack,curCountCallStack);
//              SymInfo.countNumCallstack++;
//            }
//            else{
//              curCountCallStack=SymInfo.callstack.get(curCallStack);
//            }
            List<BooleanFormula> glb;
            if(loc.getCsGlbVarErrIntp().keySet().contains(curCountCallStack)){
              glb=loc.getCsGlbVarErrIntp().get(curCountCallStack);
            }
            else{
              glb=new ArrayList<BooleanFormula>();
              loc.getCsGlbVarErrIntp().put(curCountCallStack,glb);
            }
            loc.setGlbVarErrIntp(glb,nextLoc.getGlbVarErrIntp());

            continue;
          }
          T lastItp = itpGroupsIds.get(itpSize - 1);
          itpGroupsIds.set(0, lastItp);
          itpGroupsIds.remove(itpSize - 1);
          itpSize--;
          SSAMap ssa = PredicateAbstractState
              .getPredicateState(pa.get(j + 1))
              .getAbstractionFormula().getBlockFormula().getSsa();
          BooleanFormula tsucIntp;
          //System.out.println(j+","+curState.getStateId());
          tsucIntp = fmgr.instantiate(sucIntp, ssa);
          T itpGroupId1 = itpProver.push(tsucIntp);
          itpGroupsIds.set(1, itpGroupId1);
          tToFormula.put(itpGroupId1, tsucIntp);
          if (!itpProver.isUnsat()) {
           // loc.addMayCE(SymInfo.cePF);
            break;
          }

          /*
           * for testing process
           */
          long time=System.currentTimeMillis();
          List<String> formulaStr=new ArrayList<String>();
          List<BooleanFormula> formula=new ArrayList<BooleanFormula>();
          for(int i=0;i<2;i++){
            T tt = itpGroupsIds.get(i);
            BooleanFormula mf = tToFormula.get(tt);
            formula.add(mf);
            formulaStr.add(mf.toString());
          }
          boolean tmpB=true;
          if(tmpB&&formulaStr.get(0).equals("true")){
               intp1=formula.get(1);
          }
          else if(tmpB&&formulaStr.get(1).equals("true")){
               intp1=null;
          }
          else if(tmpB){
            String newProgram="";
            List<String> func= new ArrayList<String>(1);
          try {
            newProgram=PrincessInfo.analyzeUsePrincess(formulaStr,func);
          } catch (IOException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
          }

          if(!newProgram.equals("")){

          try {
            CFA newCfa = MyInfo.parse(newProgram, func.get(0));
            CFANode mainNode = newCfa.getMainFunction();
            CFANode tmpNode=mainNode;
            List<CFAEdge> outEdges = tmpNode.getLeavingEdge();
            while(outEdges.size()==1){
               tmpNode=outEdges.get(0).getSuccessor();
               outEdges = tmpNode.getLeavingEdge();
            }
            CFAEdge edge=outEdges.get(0);
            if(edge instanceof CAssumeEdge){
              if(!((CAssumeEdge) edge).getTruthAssumption()){
                edge=outEdges.get(1);
              }
            }
            PointerTargetSetBuilder pts = MyInfo.converter.createPointerTargetSetBuilder(MyInfo.lastOldFormula.getPointerTargetSet());
            ErrorConditions errorConditions = new ErrorConditions(bfmgr);
            Constraints constraints = new Constraints(bfmgr);
            BooleanFormula newIntp = MyInfo.converter.createFormulaForEdge(edge, "main", ssa.builder(), pts, constraints, errorConditions);
            //newIntp=fmgr.uninstantiate(newIntp);
            intp1=newIntp;
            System.out.println(newIntp);
          } catch (InvalidConfigurationException | IOException | ParserException | UnrecognizedCCodeException | UnrecognizedCFAEdgeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
          }
          System.out.println("the time of princess:"+(System.currentTimeMillis()-time));
          }
         // end
         // time=System.currentTimeMillis();
          List<T> termB = itpGroupsIds.subList(2, j + 3);
          int tbsize = termB.size();
          Set<T> tmp = new HashSet<T>();
          for (int k = 0; k < tbsize; k++) {
            T ith = termB.get(k);
            if (!specialRemove.contains(ith)) {
              tmp.add(ith);
            }
          }
          List<Set<T>> sub=new ArrayList<Set<T>>();
          Set<T> tmpSet=new HashSet<T>(2);
          for(int i=0;i<2;i++){
            tmpSet.add(itpGroupsIds.get(i));
          }
          sub.add(tmpSet);
          sub.add(tmp);
          List<BooleanFormula> intpSeq = itpProver.getSeqInterpolants(sub);
          if(intp1==null) {
            intp1=intpSeq.get(0);
          }

          //System.out.println("the time of SMT:"+(System.currentTimeMillis()-time));
          //.getInterpolant1(itpGroupsIds.subList(0, 2), tmp);
          String funcname = loc.getFunctionName();

          if (intp1.toString().contains("::")
              && !intp1.toString().contains(funcname)) {
            // stop=true;
           // loc.addMayCE(SymInfo.cePF);
            break;
          }
          if (intp1.toString().equals("false")
              || intp1.toString().equals("true")) {
            //loc.addMayCE(SymInfo.cePF);
            break;
          }
          boolean isBreak=false;
          if (intp1.toString().matches(".*\\*.*")) {
            //errorIntp = SymInfo.bfmr.makeBoolean(false);
            //setCurErrIntp(loc,curCallStack,errorIntp);
            //break;
            isBreak=true;
          }
          //else {
            intp1 = fmgr.uninstantiate(intp1);
            errorIntp = fmgr.uninstantiate(errorIntp);

            if (errorIntp.toString().equals("false")) {
              errorIntp = intp1;
              errorIntp=makeNewERRORIntp(errorIntp,nextLoc,j,idLS,pa,sucCallStack);
              errIntp.put(curCountCallStack, errorIntp);
              //setCurErrIntp(loc,curCallStack,errorIntp);
              loc.setErrorIntp(errorIntp);
              loc.setEc(true);
            } else {

              if (!errorIntp.toString()
                  .contains(intp1.toString())) {
                if(errorIntp.toString().equals("true")){
                  errorIntp=intp1;
                }
                else{
                 errorIntp = fmgr.makeOr(errorIntp, intp1);
                }
                errorIntp=makeNewERRORIntp(errorIntp,nextLoc,j,idLS,pa,sucCallStack);
                errIntp.put(curCountCallStack, errorIntp);
                //setCurErrIntp(loc,curCallStack,errorIntp);
                loc.setErrorIntp(errorIntp);
                loc.setEc(true);
              }

            }
            if(isBreak){
              break;
            }
           // int curCountCallStack=-1;
//            if(!SymInfo.callstack.keySet().contains(curCallStack)){
//              curCountCallStack=SymInfo.countNumCallstack;
//              SymInfo.callstack.put(curCallStack,curCountCallStack);
//              SymInfo.countNumCallstack++;
//            }
//            else{
//              curCountCallStack=SymInfo.callstack.get(curCallStack);
//            }
            List<BooleanFormula> glb;
            if(loc.getCsGlbVarErrIntp()!=null&&loc.getCsGlbVarErrIntp().keySet().contains(curCountCallStack)){
              glb=loc.getCsGlbVarErrIntp().get(curCountCallStack);
            }
            else{
              glb=new ArrayList<BooleanFormula>();
              if(loc.getCsGlbVarErrIntp()==null){
                loc.setCsGlbVarErrIntp(new HashMap<Integer, List<BooleanFormula>>());
              }
              loc.getCsGlbVarErrIntp().put(curCountCallStack,glb);
            }
            if(!intp1.toString().contains("::")){
               glb.add(intp1);
               //loc.addGlbVarErrIntp(intp1);
            }
           // glb.
            loc.setGlbVarErrIntp(glb,nextLoc.getGlbVarErrIntp());
            if (errorIntp.toString().equals(sucIntp.toString())) {
              loc.seteIsEqSuc(true);
            } else {
              loc.seteIsEqSuc(false);
            }
          //}
          //if(loc.getNumEnteringEdges()>1){
           // loc.addMayCE(SymInfo.cePF);
          //}

        }

      }
      // time=System.currentTimeMillis()-time;
      // System.out.println(time+",");
      // System.out.println("time3=" + (System.currentTimeMillis() -
      // time3));
      return true;
    }
    private void setCurErrIntp(CFANode loc, String curCallStack, BooleanFormula errorIntp) {
      // TODO Auto-generated method stub
      Map<Integer, BooleanFormula> errIntp = loc.getErrIntp();
      int curCountCallStack=-1;
      if(!SymInfo.callstack.keySet().contains(curCallStack)){
        curCountCallStack=SymInfo.countNumCallstack;
        SymInfo.callstack.put(curCallStack,curCountCallStack);
        SymInfo.countNumCallstack++;
      }
      else{
        curCountCallStack=SymInfo.callstack.get(curCallStack);
      }
      if(errIntp==null){
        errIntp=new HashMap<Integer, BooleanFormula>();
        errIntp.put(curCountCallStack, errorIntp);
        loc.setErrIntp(errIntp);
      }
      else{
        if(errIntp.keySet().contains(curCountCallStack)){
          BooleanFormula bf=errIntp.get(curCountCallStack);
          bf=fmgr.makeOr(bf,errorIntp);
          errIntp.put(curCountCallStack, bf);
        }
        else{
          errIntp.put(curCountCallStack, errorIntp);
        }
      }
    }

    private BooleanFormula makeNewERRORIntp(BooleanFormula errorIntp, CFANode nextLoc,int j,int idLS, List<AbstractState> pa,String sucCallStack){
      List<BooleanFormula> glbIntp=null;
      if(SymInfo.callstack.keySet().contains(sucCallStack)){
          int index=SymInfo.callstack.get(sucCallStack);
          if(nextLoc.getCsGlbVarErrIntp()!=null) {
            glbIntp=nextLoc.getCsGlbVarErrIntp().get(index);
          }
      }
      if(glbIntp!=null){
        //List<BooleanFormula> glbIntp = nextLoc.getGlbVarErrIntp();
        for(BooleanFormula bf: glbIntp){
           String s=bf.toString();
           int start=0;
           boolean bs=false;
           int end=0;
           for(int i=0;i<s.length();i++){
             char ch=s.charAt(i);
             if(ch==' '&&!bs){
               start=i;
               bs=true;
             }
             else if(ch==' '&&bs){

               end=i;
               //bs=false;
               String subs=s.substring(start,end);
               start=i;
               if(subs.contains("(")||subs.contains(")")||subs.contains(".cse")){
                 continue;
               }
               if(subs.matches("[0-9]+")){
                 continue;
               }
               if(!errorIntp.toString().contains(subs))
               {
                 errorIntp=fmgr.makeAnd(errorIntp, bf);
                 break;
                 //return errorIntp;
               }
             }
           }

        }
     }
     else{
       for (int k = j+2; k<idLS - 1 ; k++) {
         ARGState state=(ARGState) pa.get(k);
           CFANode kl= state.getLoc();
           glbIntp=null;
           CompositeState sucComp = (CompositeState) state.getWrappedStates().get(0);
           List<AbstractState> sucWrap = sucComp.getWrappedStates();
           for(AbstractState abs: sucWrap){
             if(abs instanceof CallstackState){
               sucCallStack=((CallstackState) abs).getMyStack().toString();
               break;
             }
          }
           if(SymInfo.callstack.keySet().contains(sucCallStack)){
               int index=SymInfo.callstack.get(sucCallStack);
               glbIntp=kl.getCsGlbVarErrIntp().get(index);
           }
           if(glbIntp!=null){
             //List<BooleanFormula> glbIntp = kl.getGlbVarErrIntp();
             for(BooleanFormula bf: glbIntp){
                String s=bf.toString();
                int start=0;
                boolean bs=false;
                int end=0;
                for(int i=0;i<s.length();i++){
                  char ch=s.charAt(i);
                  if(ch==' '&&!bs){
                    start=i;
                    bs=true;
                  }
                  else if(ch==' '&&bs){

                    end=i;
                    //bs=false;
                    String subs=s.substring(start,end);
                    start=i;
                    if(subs.contains("(")||subs.contains(")")||subs.contains(".cse")){
                      continue;
                    }
                    if(subs.matches("[0-9]+")){
                      continue;
                    }
                    if(!errorIntp.toString().contains(subs))
                    {
                      errorIntp=fmgr.makeAnd(errorIntp, bf);
                      break;
                      //return errorIntp;
                    }
                  }
                }
             }
             break;
          }
       }
     }
      return errorIntp;
    }
    private List<BooleanFormula> makeNewERRORIntpForPrincess(BooleanFormula errorIntp, CFANode nextLoc,int j,int idLS, List<AbstractState> pa,String sucCallStack){
      List<BooleanFormula> glbIntp=null;
      if(SymInfo.callstack.keySet().contains(sucCallStack)){
          int index=SymInfo.callstack.get(sucCallStack);
          if(nextLoc.getCsGlbVarErrIntp()!=null) {
            glbIntp=nextLoc.getCsGlbVarErrIntp().get(index);
          }
      }
      if(glbIntp!=null){
        //List<BooleanFormula> glbIntp = nextLoc.getGlbVarErrIntp();
        for(BooleanFormula bf: glbIntp){
           String s=bf.toString();
           int start=0;
           boolean bs=false;
           int end=0;
           for(int i=0;i<s.length();i++){
             char ch=s.charAt(i);
             if(ch==' '&&!bs){
               start=i;
               bs=true;
             }
             else if(ch==' '&&bs){

               end=i;
               //bs=false;
               String subs=s.substring(start,end);
               start=i;
               if(subs.contains("(")||subs.contains(")")||subs.contains(".cse")){
                 continue;
               }
               if(subs.matches("[0-9]+")){
                 continue;
               }
               if(!errorIntp.toString().contains(subs))
               {
                 errorIntp=fmgr.makeOr(errorIntp, bf);
                 break;
                 //return errorIntp;
               }
             }
           }

        }
     }
     else{
       for (int k = j+2; k<idLS - 1 ; k++) {
         ARGState state=(ARGState) pa.get(k);
           CFANode kl= state.getLoc();
           glbIntp=null;
           CompositeState sucComp = (CompositeState) state.getWrappedStates().get(0);
           List<AbstractState> sucWrap = sucComp.getWrappedStates();
           for(AbstractState abs: sucWrap){
             if(abs instanceof CallstackState){
               sucCallStack=((CallstackState) abs).getMyStack().toString();
               break;
             }
          }
           if(SymInfo.callstack.keySet().contains(sucCallStack)){
               int index=SymInfo.callstack.get(sucCallStack);
               glbIntp=kl.getCsGlbVarErrIntp().get(index);
           }
           if(glbIntp!=null){
             //List<BooleanFormula> glbIntp = kl.getGlbVarErrIntp();
             for(BooleanFormula bf: glbIntp){
                String s=bf.toString();
                int start=0;
                boolean bs=false;
                int end=0;
                for(int i=0;i<s.length();i++){
                  char ch=s.charAt(i);
                  if(ch==' '&&!bs){
                    start=i;
                    bs=true;
                  }
                  else if(ch==' '&&bs){

                    end=i;
                    //bs=false;
                    String subs=s.substring(start,end);
                    start=i;
                    if(subs.contains("(")||subs.contains(")")||subs.contains(".cse")){
                      continue;
                    }
                    if(subs.matches("[0-9]+")){
                      continue;
                    }
                    if(!errorIntp.toString().contains(subs))
                    {
                      errorIntp=fmgr.makeOr(errorIntp, bf);
                      break;
                      //return errorIntp;
                    }
                  }
                }
             }
             break;
          }
       }
     }
      return null;
    }
    private int SymbolicInterpolant(List<BooleanFormula> pF,
        List<AbstractState> pa, List<T> itpGroupsIds, boolean infeasible)
        throws InterruptedException, SolverException {
      // date: 2016/10/16
      int indexErr = 0;
      SymInfo.forUninstance=true;
      // date: 2016/10/16

      // List<BooleanFormula> interpolants = new
      // ArrayList<BooleanFormula>();
      int fsize = pF.size();
      int myindex = 0;
      int numLastBra = SymInfo.lastFalse;// fsize - 1;
      ARGState lastState = (ARGState) pa.get(fsize - 1);
      CFANode lloc = lastState.getLoc();
      if (lloc == null) {
        lloc = AbstractStates.extractLocation(lastState);

        lastState.setLoc(lloc);
        if (lloc.getTrueIntp() == null) {
          lloc.setTrueIntp(SymInfo.bfmr.makeBoolean(true));
          lloc.setErrorIntp(SymInfo.bfmr.makeBoolean(true));
        }
      }
      for (int j = fsize - 1; j > 0; j--) {
        ARGState curState = (ARGState) pa.get(j);
        CFANode loc = curState.getLoc();
        loc = loc == null ? AbstractStates.extractLocation(curState)
            : loc;
        curState.setLoc(loc);
        if (loc.getNumLeavingEdges() > 1
            && loc.getLeavingEdge(0) instanceof CAssumeEdge) {

          break;
        }
        loc.setTrueFull(true);
        // loc.setErrorFull(true);
      }
      boolean isfull;
      lastState.setReached(false);

      boolean oneBra = false;
      int tmp = numLastBra;
      itpProver.close();
      itpProver = newEnvironment();
      currentlyAssertedFormulas.clear();
      int gs = numLastBra;
      itpGroupsIds = new ArrayList<>(Collections.<T> nCopies(
          numLastBra + 2, null));
      List<BooleanFormula> subPF = pF.subList(0, numLastBra + 1);
      List<Triple<BooleanFormula, AbstractState, Integer>> traceFormulas = orderFormulas(
          subPF, pa);
      ListIterator<Triple<BooleanFormula, AbstractState, Integer>> todoIterator = traceFormulas
          .listIterator();
      ListIterator<Triple<BooleanFormula, AbstractState, T>> assertedIterator = currentlyAssertedFormulas
          .listIterator();

      int firstBadIndex = -1; // index of first mis-matching formula in
                  // both lists

      while (assertedIterator.hasNext()) {
        Triple<BooleanFormula, AbstractState, T> assertedFormula = assertedIterator
            .next();

        if (!todoIterator.hasNext()) {
          firstBadIndex = assertedIterator.previousIndex();
          break;
        }

        Triple<BooleanFormula, AbstractState, Integer> todoFormula = todoIterator
            .next();

        if (todoFormula.getFirst().equals(assertedFormula.getFirst())) {
          // formula is already in solver stack in correct location
          @SuppressWarnings("unchecked")
          T itpGroupId = assertedFormula.getThird();
          itpGroupsIds.set(todoFormula.getThird(), itpGroupId);
          myindex = todoFormula.getThird();

        } else {
          firstBadIndex = assertedIterator.previousIndex();
          // rewind iterator by one so that todoFormula will be added
          // to stack
          todoIterator.previous();
          break;
        }
      }

      // now remove the formulas from the solver stack where necessary
      if (firstBadIndex == -1) {
        // solver stack was already empty, nothing do to

      } else if (firstBadIndex == 0) {
        // Create a new environment instead of cleaning up the old one
        // if no formulas need to be reused.
        itpProver.close();
        itpProver = newEnvironment();
        currentlyAssertedFormulas.clear();

      } else {
        assert firstBadIndex > 0;
        // list with all formulas on solver stack that we need to remove
        // (= remaining formulas in currentlyAssertedFormulas list)
        List<Triple<BooleanFormula, AbstractState, T>> toDeleteFormulas = currentlyAssertedFormulas
            .subList(firstBadIndex,
                currentlyAssertedFormulas.size());

        // remove formulas from solver stack
        for (int i = 0; i < toDeleteFormulas.size(); i++) {
          itpProver.pop();
        }
        toDeleteFormulas.clear(); // this removes from
                      // currentlyAssertedFormulas

        reusedFormulasOnSolverStack += currentlyAssertedFormulas.size();
      }

      boolean isStillFeasible = true;

      if (incrementalCheck && !currentlyAssertedFormulas.isEmpty()) {
        if (itpProver.isUnsat()) {
          isStillFeasible = false;
        }
      }

      // add remaining formulas to the solver stack
      while (todoIterator.hasNext()) {
        Triple<BooleanFormula, AbstractState, Integer> p = todoIterator
            .next();
        BooleanFormula f = p.getFirst();
        AbstractState state = p.getSecond();
        int index = p.getThird();

        assert itpGroupsIds.get(index) == null;
        T itpGroupId = itpProver.push(f);
        itpGroupsIds.set(index, itpGroupId);
        myindex = index;
        // currentlyAssertedFormulas.add(Triple.of(f, state,
        // itpGroupId));

        if (incrementalCheck && isStillFeasible && !bfmgr.isTrue(f)) {
          if (itpProver.isUnsat()) {
            // We need to iterate through the full loop
            // to add all formulas, but this prevents us from doing
            // further sat checks.
            isStillFeasible = false;
          }
        }
      }
      int firstBra = 0;
      boolean hasFound = false;
      // itpGroupsIds.remove(fsize-1);
      // itpProver.pop();
      boolean change = false;
      List<CFAEdge> nnEdge = null;
      // boolean testB=false;
      for (int j = SymInfo.lastFalse - 1; j >= 1; j--) {

        ARGState curState = (ARGState) pa.get(j);
        ARGState sucState = (ARGState) pa.get(j + 1);
        CFANode loc = curState.getLoc();
        CFANode nextLoc = sucState.getLoc();
        BooleanFormula nextTrueIntp = nextLoc.getTrueIntp();
        // System.out.println("j="+j);
        if (loc == null) {
          loc = AbstractStates.extractLocation(curState);
          curState.setLoc(loc);
        }
        int lnd = loc.getNodeNumber();
        List<CFAEdge> e = curState.getEdgesToChild(sucState);
        if (SymInfo.nodeIds.contains(lnd)) {
          // stopWeight=true;
        } else {
          SymInfo.nodeIds.add(lnd);
        }
        if (oneBra) {
          ARGState preState = (ARGState) pa.get(j - 1);
          CFANode pLoc = preState.getLoc();
          List<CFAEdge> edge = preState.getEdgesToChild(curState);
          if (SymInfo.weight) {
            SymInfo.setWeight(curState, sucState, edge);
            continue;
          } else {
            break;
          }
        }

        if (!sucState.isReached() && SymInfo.result != Result.FALSE) {
          nextTrueIntp = SymInfo.bfmr.makeBoolean(false);
          if (nextLoc.getTrueIntp() != null
              && nextLoc.getTrueIntp().toString().equals("true")) {
            nextLoc.setTrueIntp(nextTrueIntp);
          }
        }
        BooleanFormula trueIntp = loc.getTrueIntp();
        // testB=false;
        if (loc.getNumEnteringEdges() == 1
            && loc.getEnteringEdge(0) instanceof CAssumeEdge) {
        } else if (loc.getNumLeavingEdges() > 1
            && loc.getLeavingEdge(0) instanceof CAssumeEdge) {
        } else {
          if (!sucState.isReached()) {
            curState.setReached(false);// unreachable
            itpGroupsIds.remove(j + 1);
            itpProver.pop();
            isfull = SymInfo.isTrueFull(loc);
            if (isfull) {
              loc.setTrueFull(true);
              ARGState preState = (ARGState) pa.get(j - 1);
              List<CFAEdge> edge = preState.getEdgesToChild(curState);
              for(int i=0;i<edge.size();i++){
                CFAEdge eth = edge.get(i);
                eth.getSuccessor().setTrueFull(true);
               }
            } else {
              loc.setTrueFull(false);
            }
            nnEdge = e;
            continue;
          }

        }
        itpProver.pop();
        itpGroupsIds.set(j + 1, null);

        boolean b;
        if (!hasFound) {
          b = itpProver.isUnsat();
          if (b) {
            indexErr = j;
            curState.setReached(false);
            SymInfo.furState = curState;
            // itpProver.pop();
            itpGroupsIds.remove(j + 1);
            // nnEdge=e;
            if (loc.isTrueFull()) {
              continue;
            }
            isfull = SymInfo.isTrueFull(loc);
            if (isfull) {
              loc.setTrueFull(true);
              ARGState preState = (ARGState) pa.get(j - 1);
              List<CFAEdge> edge = preState.getEdgesToChild(curState);
              for(int i=0;i<edge.size();i++){
                CFAEdge eth = edge.get(i);
                eth.getSuccessor().setTrueFull(true);
               }
            } else {
              loc.setTrueFull(false);
            }

            continue;
          } else {
            // nnEdge.setWeight(0);
          }
        }
        hasFound = true;
        // if (loc.isTrueFull() && !trueIntp.toString().equals("false"))
        // {
        // itpGroupsIds.remove(j+1);
        // interpolants.add(fmgr.instantiate(trueIntp, SymInfo.ssa));
        // continue;
        // }
        List<Triple<BooleanFormula, AbstractState, Integer>> traceFormulas1 = traceFormulas
            .subList(j + 1, j + 2);
        int popSize = traceFormulas1.size();
        todoIterator = traceFormulas1.listIterator();
        assertedIterator = currentlyAssertedFormulas.listIterator();

        // int firstBadIndex = -1; // index of first mis-matching
        // formula in both lists

        while (assertedIterator.hasNext()) {
          Triple<BooleanFormula, AbstractState, T> assertedFormula = assertedIterator
              .next();

          if (!todoIterator.hasNext()) {
            firstBadIndex = assertedIterator.previousIndex();
            break;
          }

          Triple<BooleanFormula, AbstractState, Integer> todoFormula = todoIterator
              .next();

          if (todoFormula.getFirst().equals(
              assertedFormula.getFirst())) {
            // formula is already in solver stack in correct
            // location
            @SuppressWarnings("unchecked")
            T itpGroupId = assertedFormula.getThird();
            itpGroupsIds.set(todoFormula.getThird(), itpGroupId);
            myindex = todoFormula.getThird();

          } else {
            firstBadIndex = assertedIterator.previousIndex();
            // rewind iterator by one so that todoFormula will be
            // added to stack
            todoIterator.previous();
            break;
          }
        }

        // now remove the formulas from the solver stack where necessary
        if (firstBadIndex == -1) {
          // solver stack was already empty, nothing do to

        } else if (firstBadIndex == 0) {
          // Create a new environment instead of cleaning up the old
          // one
          // if no formulas need to be reused.
          itpProver.close();
          itpProver = newEnvironment();
          currentlyAssertedFormulas.clear();

        } else {
          assert firstBadIndex > 0;
          // list with all formulas on solver stack that we need to
          // remove
          // (= remaining formulas in currentlyAssertedFormulas list)
          List<Triple<BooleanFormula, AbstractState, T>> toDeleteFormulas = currentlyAssertedFormulas
              .subList(firstBadIndex,
                  currentlyAssertedFormulas.size());

          // remove formulas from solver stack
          for (int i = 0; i < toDeleteFormulas.size(); i++) {
            itpProver.pop();
          }
          toDeleteFormulas.clear(); // this removes from
          // currentlyAssertedFormulas

          reusedFormulasOnSolverStack += currentlyAssertedFormulas
              .size();
        }

        isStillFeasible = true;

        if (incrementalCheck && !currentlyAssertedFormulas.isEmpty()) {
          if (itpProver.isUnsat()) {
            isStillFeasible = false;
          }
        }

        // add remaining formulas to the solver stack
        while (todoIterator.hasNext()) {
          Triple<BooleanFormula, AbstractState, Integer> p = todoIterator
              .next();
          BooleanFormula f = p.getFirst();
          AbstractState state = p.getSecond();
          int index = p.getThird();

          assert itpGroupsIds.get(index) == null;
          T itpGroupId = itpProver.push(f);
          itpGroupsIds.set(index, itpGroupId);
          myindex = index;
          // currentlyAssertedFormulas.add(Triple.of(f, state,
          // itpGroupId));

          if (incrementalCheck && isStillFeasible && !bfmgr.isTrue(f)) {
            if (itpProver.isUnsat()) {
              // We need to iterate through the full loop
              // to add all formulas, but this prevents us from
              // doing further sat checks.
              isStillFeasible = false;
            }
          }
        }

        gs = itpGroupsIds.size();
        PredicateAbstractState element = PredicateAbstractState
            .getPredicateState(sucState);
        SymInfo.ssa = element.getAbstractionFormula().getBlockFormula()
            .getSsa();
        int isize = itpGroupsIds.size();
        BooleanFormula tmpNTIntp;
        if (nextTrueIntp.toString().equals("false")) {
          tmpNTIntp = nextTrueIntp;
        } else {
          tmpNTIntp = fmgr.makeNot(nextTrueIntp);
        }
        ARGState preState = (ARGState) pa.get(j - 1);
        CFANode pLoc = preState.getLoc();
        List<CFAEdge> edge = preState.getEdgesToChild(curState);
        tmpNTIntp = fmgr.instantiate(tmpNTIntp, SymInfo.ssa);
        T itpGroupId;
        itpGroupId = itpProver.push(tmpNTIntp);
        itpGroupsIds.set(isize - 1, itpGroupId);
        b = itpProver.isUnsat();
        if (!b) {
          oneBra = true;
          if (SymInfo.weight) {
            SymInfo.setWeight(curState,sucState, edge);
          }
          continue;
        }
        BooleanFormula intp;

        intp = itpProver.getInterpolant(itpGroupsIds.subList(0, j + 1));

        itpGroupsIds.set(isize - 1, null);
        itpProver.pop();
        itpProver.pop();
        itpGroupsIds.remove(j + 1);

        if (!loc.isTrueFull()) {
          isfull = SymInfo.isTrueFull(loc);
          // CFAEdge e = loc.getEdgeTo(nextLoc);
          if (isfull) {
            loc.setTrueFull(true);
            for(int i=0;i<edge.size();i++){
             CFAEdge eth = edge.get(i);
             eth.getSuccessor().setTrueFull(true);
            }

            if (SymInfo.weight) {
              for(int i=0;i<edge.size();i++){
                 edge.get(i).setWeight(0);
              }
              // if (e instanceof CAssumeEdge) {
              // Collections.sort(loc.getLeavingEdge(),
              // new Comparator<CFAEdge>() {
              // @Override
              // public int compare(CFAEdge e1,
              // CFAEdge e2) {
              // Integer w1 = e1.getWeight();
              // Integer w2 = e2.getWeight();
              // return w1.compareTo(w2);
              // }
              // });
               }
          } else {
            if (SymInfo.weight) {
              List<CFAEdge> lEdges = loc.getLeavingEdge();
              int weight = 0;
              if (e instanceof CAssumeEdge) {
                for (CFAEdge le : lEdges) {
                  if (le.getWeight() == -1) {
                    weight += 1;
                  } else {
                    weight += le.getWeight();
                  }
                }
                for(int i=0;i<edge.size();i++){
                  edge.get(i).setWeight(weight);
                }
                Collections.sort(loc.getLeavingEdge(),
                    new Comparator<CFAEdge>() {
                      @Override
                      public int compare(CFAEdge e1, CFAEdge e2) {
                        Integer w1 = e1.getWeight() == -1 ? 1
                            : e1.getWeight();
                        Integer w2 = e2.getWeight() == -1 ? 1
                            : e2.getWeight();
                        return w1.compareTo(w2);
                      }
                    });
              } else {
                for(int i=0;i<edge.size();i++){
                   edge.get(0).setWeight(e.get(0).getWeight());
                }
              }
            }
            if (loc.isLoopStart() && !(loc instanceof CLabelNode)) {
              if (e instanceof CAssumeEdge) {
                if (!((CAssumeEdge) e).getTruthAssumption()
                    && nextLoc.isTrueFull()) {
                  loc.setTrueFull(true);
                  for(int i=0;i<edge.size();i++){
                    CFAEdge eth = edge.get(i);
                    eth.getSuccessor().setTrueFull(true);
                   }
                } else {
                  oneBra = true;
                  loc.setTrueFull(false);
                  continue;
                }
              } else {
                oneBra = true;
                loc.setTrueFull(false);
                continue;
              }
            } else {
              oneBra = true;
              loc.setTrueFull(false);
            //  continue;
            }

          }
        }
        // nnEdge=e;
        if (intp.toString().matches(".*\\*.*")) {
          oneBra = true;
          // //break;
          continue;
        } else {
          intp = fmgr.uninstantiate(intp);
          trueIntp = fmgr.uninstantiate(trueIntp);
          if (!trueIntp.toString().equals("false")) {
            if (!trueIntp.toString().contains(intp.toString())) {
              trueIntp = fmgr.makeAnd(trueIntp, intp);
              loc.setTrueIntp(trueIntp);
              loc.setSc(true);
            }
            // else{
            // loc.setSc(true);
            // }

          } else {
            trueIntp = intp;
            loc.setSc(true);
          }
          if (trueIntp.toString().equals(nextTrueIntp.toString())) {
            loc.setsIsEqSuc(true);
          } else {
            // trueIntp = fmgr.makeAnd(trueIntp, nextTrueIntp);
            loc.setsIsEqSuc(false);
          }

        }

        loc.setTrueIntp(trueIntp);
      }
      itpProver.close();
      itpProver = newEnvironment();
      currentlyAssertedFormulas.clear();
      return 0;
    }
  }
}
