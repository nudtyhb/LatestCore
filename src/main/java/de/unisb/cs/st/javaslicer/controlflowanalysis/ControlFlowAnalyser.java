/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.controlflowanalysis
 *    Class:     ControlFlowAnalyser
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/controlflowanalysis/ControlFlowAnalyser.java
 *
 * This file is part of the JavaSlicer tool, developed by Clemens Hammacher at Saarland University.
 * See http://www.st.cs.uni-saarland.de/javaslicer/ for more information.
 *
 * JavaSlicer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaSlicer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JavaSlicer. If not, see <http://www.gnu.org/licenses/>.
 */
package de.unisb.cs.st.javaslicer.controlflowanalysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.Map.Entry;

import de.hammacher.util.UniqueQueue;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionType;
import de.unisb.cs.st.javaslicer.common.classRepresentation.ReadMethod;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.LabelMarker;
import de.unisb.cs.st.javaslicer.controlflowanalysis.ControlFlowGraph.AbstractInstrNode;
import de.unisb.cs.st.javaslicer.controlflowanalysis.ControlFlowGraph.InstrNode;
import de.unisb.cs.st.javaslicer.controlflowanalysis.ReachabilityNodeFactory.ReachInstrNode;

public class ControlFlowAnalyser {

    private static ControlFlowAnalyser instance = new ControlFlowAnalyser();

    private ControlFlowAnalyser() {
        // private constructor
    }

    public static ControlFlowAnalyser getInstance() {
        return instance;
    }

    /**
     * Computes the (inverted) control dependences for one method.
     *
     * @param method the method for which the dependences are computed
     * @return a map that contains for every instruction all instructions that are dependent on this one
     */
    // 基于控制流图计算出一个方法的控制依赖图!
    // 结果是每条指令所对应的所有依赖于这条指令的指令集合！
    public Map<Instruction, Set<Instruction>> getInvControlDependences(ReadMethod method) {
        Map<Instruction, Set<Instruction>> invControlDeps = new HashMap<Instruction, Set<Instruction>>();
        Set<Instruction> emptyInsnSet = Collections.emptySet();
        // 返回这个方法的控制流图
        ControlFlowGraph graph = new ControlFlowGraph(method, ReachabilityNodeFactory.getInstance());
        computeReachableNodes(graph); // 计算出CFG中每个节点的reachable 和 surelyreachable信息！
        // 下面计算每一条指令的控制依赖集合！
        for (Instruction insn: method.getInstructions()) {
            InstrNode node = graph.getNode(insn);
            ReachInstrNode reachNode = (ReachabilityNodeFactory.ReachInstrNode)node; 
            // 当指令为LABEL节点时！
            if (insn.getType() == InstructionType.LABEL) {
                LabelMarker label = (LabelMarker) insn;
                if (label.isCatchBlock()) {
                    Set<AbstractInstrNode> executedIfException = reachNode.getSurelyReached();
                    InstrNode node2 = graph.getNode(
                            method.getInstructions().iterator().next());
                    Set<AbstractInstrNode> availableWithoutException = ((ReachInstrNode)node2).getReachable();
                    Set<Instruction> deps = new HashSet<Instruction>();
                    for (InstrNode succ: executedIfException) {
                        if (!availableWithoutException.contains(succ) && succ.getInstruction() != insn)
                            deps.add(succ.getInstruction());
                    }
                    invControlDeps.put(insn, deps.isEmpty() ? emptyInsnSet : deps);
                } else {
                	// LABELMARKER的控制依赖指令集合为空！因为L0,L1等标记并不能改变执行流程！
                    invControlDeps.put(insn, emptyInsnSet);
                }
            } //节点的出度大于1 
            else if (node.getOutDegree() > 1) {
                assert node.getOutDegree() == node.getSuccessors().size();
                // 该列表存放分支的各个后继的所有一定可达指令集合！
                List<Set<AbstractInstrNode>> succAvailableNodes = new ArrayList<Set<AbstractInstrNode>>(node.getOutDegree());
                // 该集合存放所有后继的一定可达节点的并！
                Set<AbstractInstrNode> allInstrNodes = new HashSet<AbstractInstrNode>();
                for (InstrNode succ: node.getSuccessors()) {
                    ReachInstrNode reachSucc = (ReachInstrNode) succ;
                    Set<AbstractInstrNode> availableNodes = reachSucc.getSurelyReached();
                    succAvailableNodes.add(availableNodes);
                    allInstrNodes.addAll(availableNodes); // 计算出了Node的所有后继一定可达节点集合的并！
                }
                // 控制依赖2层含义：1.首先存在从Node出发的一种选择，该选择一定可达该指令！2. 存在从Node出发的一种选择，从该选择出发不一定可达改指令！
                Set<Instruction> deps = new HashSet<Instruction>();
                for (InstrNode succ: allInstrNodes) {
                    for (Set<AbstractInstrNode> succAv: succAvailableNodes)
                        if (!succAv.contains(succ)) // 表明Node的后继中，只要有一个对于改指令不一定可达，这个条件表明可以by passing 这条指令！
                            deps.add(succ.getInstruction());
                }
                invControlDeps.put(insn, deps.isEmpty() ? emptyInsnSet : deps);
            } else {
            	// 出度为1，表明该指令不存再控制关系，所以它的依赖集合为空！！
                invControlDeps.put(insn, emptyInsnSet);
            }
        }
       /* if(method.getName().contains("main")){
        	for(Entry<Instruction, Set<Instruction>> entry22: invControlDeps.entrySet()){
        		System.out.println("index of Instr: ");
        		System.out.print(entry22.getKey().getIndex());
        		System.out.println(" ---its dependence is :  ");
        		Iterator<Instruction> itr1=entry22.getValue().iterator();
        		while(itr1.hasNext()){
        	    Instruction aa1=itr1.next();
        	    System.out.print(aa1.getIndex());
        	    System.out.println("------");
        		}
        		System.out.println("\n");
        	}
        }*/
        return invControlDeps;
    }

    
    // 这一步的目的是为CFG中的每一个节点增加reachable 和 surelyreachable信息！
    private void computeReachableNodes(ControlFlowGraph cfg) {
    	// 唯一性队列！， true表明一个节点取出后可以再进入!
        UniqueQueue<InstrNode> queue = new UniqueQueue<InstrNode>(true);
        InstrNode node;
        // 利用random来在FIFO和LIFO之间切换！
        // using this random to switch between FIFO and LIFO behaviour turned out
        // to decrease the runtime a lot.
        // on an example method with 706 nodes (the critical one in a big example run):
        // - LIFO: 9.55 seconds
        // - FIFO: 1.88 seconds
        // - 0.5*LIFO + 0.5*FIFO: 0.23 seconds
        Random rand = new Random();

        // first, compute the reachable nodes:
        for (Instruction instr: cfg.getMethod().getInstructions())
        	// 有一个set和queue一样增加，如果插入的元素在set中，那么谁都不更新，否则2者都更新！set用来确保queue的唯一性！
            queue.add(cfg.getNode(instr)); // 队列中插入指令节点，保证了队列中元素的唯一性！
        // 当前面的设置为true时，会导致poll队列的同时，集合中也对应poll，所以才会带来一个元素在保证队列唯一性的前提下的可重复插入！
        while ((node = queue.poll()) != null) { //从队列中取出第一个元素
            Iterator<InstrNode> succIt = node.getSuccessors().iterator();
            if (succIt.hasNext()) { // 后继非空，表明该节点有可达节点！
                boolean change = false;
                ReachInstrNode reachNode = (ReachInstrNode) node;
                // 返回node的所有可达节点集合reachable
                Set<AbstractInstrNode> reachable = reachNode.getReachable();
                while (succIt.hasNext()) {
                    ReachInstrNode succ = (ReachInstrNode) succIt.next();
                    // 没有后继的节点的getReachable 是它本身！
                    change |= reachable.addAll(succ.getReachable()); // 将后继的所有可达加入到本人的所有可达中！，如果reachable 改变了，就会导致change变为true!
                }
                // 遍历所有后继以后，change表明需要迭代求不动点！！
                if (change) {
                	// 取出node所有前驱节点，因为已经将自身的可达计算出来了，下一步就是要向上传递！
                    for (InstrNode pred : node.getPredecessors()) {
                        if (rand.nextBoolean())
                            queue.addLast(pred);
                        else
                            queue.addFirst(pred);
                    }
                }
            }
        }

        // then, compute the surely reached nodes:
        //经过上面计算，queue已经排空，重新进行计算surely reachable!
        for (Instruction instr: cfg.getMethod().getInstructions())
            queue.add(cfg.getNode(instr));
        while ((node = queue.poll()) != null) {
            Iterator<InstrNode> succIt = node.getSuccessors().iterator();
            if (succIt.hasNext()) {
                boolean change = false;
                ReachInstrNode reachNode = (ReachInstrNode) node;
                ReachInstrNode succ1 = (ReachInstrNode) succIt.next();
                if (succIt.hasNext()) { // more than one successor?
                    Set<AbstractInstrNode> surelyReached = new HashSet<AbstractInstrNode>(succ1.getSurelyReached());
                    do {
                        ReachInstrNode succ2 = (ReachInstrNode) succIt.next();
                        surelyReached.retainAll(succ2.getSurelyReached()); // 求交集！！
                    } while (succIt.hasNext());
                    change |= reachNode.getSurelyReached().addAll(surelyReached);
                } else {
                	// 只有一个后继的时候，直接添加后继的一定可达就行！
                    change |= reachNode.getSurelyReached().addAll(succ1.getSurelyReached());
                }
                // change表明需要迭代求不动点！！
                if (change) {
                    for (InstrNode pred : node.getPredecessors()) {
                        if (rand.nextBoolean())
                            queue.addLast(pred);
                        else
                            queue.addFirst(pred);
                    }
                }
            }
        }
    }
}
