package iiitd.po14.copyprop;

/* Soot - a J*va Optimization Framework
 * Copyright (C) 2008 Eric Bodden
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */
import java.util.List;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.G;
import soot.Local;
import soot.PackManager;
import soot.Timers;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.Stmt;
import soot.jimple.StmtBody;
import soot.options.CPOptions;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.toolkits.scalar.LocalDefs;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.SmartLocalDefs;
import soot.util.Chain;


public class CopyPropOpt {

	public static void main(String[] args) {
		PackManager.v().getPack("jtp").add(
				new Transform("jtp.myTransform", new BodyTransformer() {

					@SuppressWarnings({ "rawtypes", "unchecked" })
					protected void internalTransform(Body body, String phase, Map opts) {
						new SimpleCopyPropagationAnalysis(new ExceptionalUnitGraph(body));
						// use G.v().out instead of System.out so that Soot can
						// redirect this output to the Eclipse console
						G.v().out.println(body.getMethod());
						
						CPOptions options = new CPOptions( opts );
				        StmtBody stmtBody = (StmtBody)body;
				        int fastCopyPropagationCount = 0;
				        int slowCopyPropagationCount = 0;
				        
				        if(Options.v().verbose())
				            G.v().out.println("[" + stmtBody.getMethod().getName() +
				                "] Propagating copies...");

				        if(Options.v().time())
				            Timers.v().propagatorTimer.start();                
				                
				        Chain units = stmtBody.getUnits();

				        Map<Local, Integer> localToDefCount = new HashMap<Local, Integer>();
				        
				        // Count number of definitions for each local.
				        {
				            Iterator stmtIt = units.iterator();
				        
				            while(stmtIt.hasNext())
				            {
				                Stmt s = (Stmt) stmtIt.next();
				                
				                if(s instanceof DefinitionStmt &&
				                    ((DefinitionStmt) s).getLeftOp() instanceof Local)
				                {
				                    Local l = (Local) ((DefinitionStmt) s).getLeftOp();
				                     
				                    if(!localToDefCount.containsKey(l))
				                        localToDefCount.put(l, new Integer(1));
				                    else 
				                        localToDefCount.put(l, new Integer(localToDefCount.get(l).intValue() + 1));
				                }
				                
				            }
				        }
				        
//				            ((JimpleBody) stmtBody).printDebugTo(new java.io.PrintWriter(G.v().out, true));
				            
				        ExceptionalUnitGraph graph = new ExceptionalUnitGraph(stmtBody);

				        LocalDefs localDefs;
				        
				        localDefs = new SmartLocalDefs(graph, new SimpleLiveLocals(graph));

				        // Perform a local propagation pass.
				        {
				            Iterator stmtIt = (new PseudoTopologicalOrderer()).newList(graph,false).iterator();

				            while(stmtIt.hasNext())
				            {
				                Stmt stmt = (Stmt) stmtIt.next();
				                Iterator useBoxIt = stmt.getUseBoxes().iterator();

				                while(useBoxIt.hasNext())
				                {
				                    ValueBox useBox = (ValueBox) useBoxIt.next();

				                    if(useBox.getValue() instanceof Local)
				                    {
				                        Local l = (Local) useBox.getValue();

				                        if(options.only_regular_locals() && l.getName().startsWith("$"))
				                            continue;
				       
				                        if(options.only_stack_locals() && !l.getName().startsWith("$"))
				                            continue;
				                            
				                        List<Unit> defsOfUse = localDefs.getDefsOfAt(l, stmt);

				                        if(defsOfUse.size() == 1)
				                        {
				                            DefinitionStmt def = (DefinitionStmt) defsOfUse.get(0);

				                            if(def.getRightOp() instanceof Local)
				                            {
				                                Local m = (Local) def.getRightOp();

				                                if(l != m)
				                                {   
				                                    Object dcObj = localToDefCount.get(m);

				                                    if (dcObj == null)
				                                        throw new RuntimeException("Variable " + m + " used without definition!");

				                                    int defCount = ((Integer)dcObj).intValue();
				                                    
				                                    if(defCount == 0)
				                                        throw new RuntimeException("Variable " + m + " used without definition!");
				                                    else if(defCount == 1)
				                                    {
				                                        useBox.setValue(m);
				                                        fastCopyPropagationCount++;
				                                        continue;
				                                    }

				                                    List<Unit> path = graph.getExtendedBasicBlockPathBetween(def, stmt);
				                                    
				                                    if(path == null)
				                                    {
				                                        // no path in the extended basic block
				                                        continue;
				                                    }
				                                     
				                                    Iterator<Unit> pathIt = path.iterator();
				                                    
				                                    // Skip first node
				                                        pathIt.next();
				                                        
				                                    // Make sure that m is not redefined along path
				                                    {
				                                        boolean isRedefined = false;
				                                        
				                                        while(pathIt.hasNext())
				                                        {
				                                            Stmt s = (Stmt) pathIt.next();
				                                            
				                                            if(stmt == s)
				                                            {
				                                                // Don't look at the last statement 
				                                                // since it is evaluated after the uses
				                                                
				                                                break;
				                                            }   
				                                            if(s instanceof DefinitionStmt)
				                                            {
				                                                if(((DefinitionStmt) s).getLeftOp() == m)
				                                                {
				                                                    isRedefined = true;
				                                                    break;
				                                                }        
				                                            }
				                                        }
				                                        
				                                        if(isRedefined)
				                                            continue;
				                                            
				                                    }
				                                    
				                                    useBox.setValue(m);
				                                    slowCopyPropagationCount++;
				                                }
				                            }
				                        }
				                    }

				                 }
				            }
				        }


				        if(Options.v().verbose())
				            G.v().out.println("[" + stmtBody.getMethod().getName() +
				                "]     Propagated: " +
				                fastCopyPropagationCount + " fast copies  " +
				                slowCopyPropagationCount + " slow copies");
				     
				        if(Options.v().time())
				            Timers.v().propagatorTimer.end();
				    
				    
						
						
						
					}
					
				}));
		
		soot.Main.main(args);
	}

	@SuppressWarnings("rawtypes")
	public static class SimpleCopyPropagationAnalysis extends ForwardFlowAnalysis {

		@SuppressWarnings("unchecked")
		public SimpleCopyPropagationAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
			super(exceptionalUnitGraph);
			//TODO remove doanalysis comment after all other todo's are over
			doAnalysis();
		}

		@Override
		protected void flowThrough(Object in, Object d, Object out) {
			// TODO function to transform the input to the output
			FlowSet FlowIn = (FlowSet) in,
					FlowOut = (FlowSet) out;
			Stmt s = (Stmt) d;
			/*Iterator rhs = 	s.getUseBoxes().iterator(),
					 lhs = s.getDefBoxes().iterator();
			*/
			
			FlowOut.clear();
			FlowIn.copy(FlowOut);
			
			// Take out kill set:
			// for each local v def’d in
			// this unit, remove v from FlowIn
			if (s instanceof AssignStmt){
			for (ValueBox box : s.getDefBoxes()){
				Value value = box.getValue();
				G.v().out.println("value is " + value);
				if( value instanceof Local )
					FlowOut.remove( value );
			}
			// Add gen set
			// for each local v used in
			// this unit, add v to FlowIn
			for (ValueBox box : s.getUseBoxes()){
				Value value = box.getValue();
				if (value instanceof Local){
					if (!FlowOut.contains(value))
						FlowOut.add(value);
				}
			}
			}
			
		}

		@Override
		protected Object newInitialFlow() {
			return new ArraySparseSet();
		}

		@Override
		protected Object entryInitialFlow() {
			return new ArraySparseSet();
		}

		@Override
		protected void merge(Object in1, Object in2, Object out) {
			FlowSet inSet1 = (FlowSet) in1,
					inSet2 = (FlowSet) in2,
					outSet = (FlowSet) out;
			inSet1.union(inSet2, outSet);	//the merge operator is union
			
		}

		@Override
		protected void copy(Object source, Object dest) {
			FlowSet sourceSet = (FlowSet) source,
					destSet = (FlowSet) dest;
					sourceSet.copy(destSet);
		}
		

	}

}