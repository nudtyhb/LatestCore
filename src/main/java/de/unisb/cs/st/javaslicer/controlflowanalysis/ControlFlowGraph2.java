/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.controlflowanalysis
 *    Class:     ControlFlowGraph
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/controlflowanalysis/ControlFlowGraph.java
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

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Queue;

import org.objectweb.asm.Opcodes;

import de.hammacher.util.UniqueQueue;
//import de.hammacher.util.graph.Graph;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionType;
import de.unisb.cs.st.javaslicer.common.classRepresentation.ReadMethod;
import de.unisb.cs.st.javaslicer.common.classRepresentation.TryCatchBlock;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.AbstractInstruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.JumpInstruction2;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.LabelMarker;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.LookupSwitchInstruction2;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.TableSwitchInstruction2;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.VarInstruction;

/**
 * A representation of the <b>control flow graph (CFG)</b> for one method.
 *
 * @author Clemens Hammacher
 */
public class ControlFlowGraph2 implements Graph<ControlFlowGraph2.InstrNode> {


    public static class InstrList extends AbstractList<InstrNode> {

        private final InstrNode[] nodes;
        // 存放的是非空节点在nodes中的编号！
        private final int[] nonNullPositions;

        public InstrList(InstrNode[] nodes, int[] nonNullPositions) {
            this.nodes = nodes;
            this.nonNullPositions = nonNullPositions;
        }

        @Override
        public InstrNode get(int index) {
            if (index < 0 || index >= this.nonNullPositions.length)
                throw new IndexOutOfBoundsException();
            return this.nodes[this.nonNullPositions[index]];
        }

        @Override
        public int size() {
            return this.nonNullPositions.length;
        }

    }

    /**
     * Representation of one node in the CFG.
     *
     * @author Clemens Hammacher
     */
    public static interface InstrNode extends Graph.Node<InstrNode> {

        /**
         * Returns the number of outgoing edges from this node.
         * @return the out degree of the node
         */
        int getOutDegree();

        /**
         * Returns the number of incoming edges of this node.
         * @return the in degree of the node
         */
        int getInDegree();

        // concretisation:
        @Override
		Collection<InstrNode> getSuccessors();

        Collection<InstrNode> getPredecessors();

        Instruction getInstruction();

        /**
         * For internal use only
         */
        void addSuccessor(InstrNode successor);
        /**
         * For internal use only
         */
        void addPredecessor(InstrNode predecessor);

        ControlFlowGraph2 getGraph();

    }

    /**
     * Basic implementation of the interface {@link InstrNode}.
     *
     * @author Clemens Hammacher
     */
    //节点信息包括：属于的CFG，属于的指令，后继节点结合，前驱节点集合
    // 添加前驱和后继，得出出度和入度！
    public static class AbstractInstrNode implements InstrNode {

        private final List<InstrNode> successors = new ArrayList<InstrNode>(0);
        private final List<InstrNode> predecessors = new ArrayList<InstrNode>(0);
        private final Instruction instruction;
        private final ControlFlowGraph2 cfg;

        public AbstractInstrNode(ControlFlowGraph2 cfg, Instruction instr) {
            if (cfg == null || instr == null)
                throw new NullPointerException();
            this.cfg = cfg;
            this.instruction = instr;
        }

        @Override
		public Instruction getInstruction() {
            return this.instruction;
        }

        @Override
		public Collection<InstrNode> getSuccessors() {
            return this.successors;
        }

        @Override
		public Collection<InstrNode> getPredecessors() {
            return this.predecessors;
        }

        @Override
		public int getOutDegree() {
            return this.successors.size();
        }

        @Override
		public int getInDegree() {
            return this.predecessors.size();
        }

        @Override
		public void addSuccessor(InstrNode successor) {
            this.successors.add(successor);
        }

        @Override
		public void addPredecessor(InstrNode predecessor) {
            this.predecessors.add(predecessor);
        }

        @Override
        public int hashCode() {
            return this.instruction.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            AbstractInstrNode other = (AbstractInstrNode) obj;
            if (!this.instruction.equals(other.instruction))
                return false;
            return true;
        }

        @Override
        public String toString() {
            return this.instruction.toString();
        }

        @Override
		public ControlFlowGraph2 getGraph() {
            return this.cfg;
        }

        @Override
		public String getLabel() {
            return toString();
        }

    }

    public interface NodeFactory {

        InstrNode createNode(ControlFlowGraph2 cfg, Instruction instruction);

    }

    public static class AbstractNodeFactory implements NodeFactory {

        @Override
		public InstrNode createNode(ControlFlowGraph2 cfg, Instruction instr) {
            return new AbstractInstrNode(cfg, instr);
        }

    }

    public ReadMethod method;
    public final InstrNode[] instructionNodes;
    private int[] nonNullPositions;

    /**
     * Computes the <b>control flow graph</b> for one method, using the usual
     * {@link AbstractNodeFactory}.
     *
     * @param method the method for which the CFG is computed
     */
    // 仅仅对于一特定方法计算CFG
    public ControlFlowGraph2(ReadMethod method) {
        this(method, new AbstractNodeFactory());
    }

    /**
     * Computes the <b>control flow graph</b> for one method.
     *
     * @param method the method for which the CFG is computed
     * @param nodeFactory the factory that creates the nodes of the CFG
     */
    // 第一个参数表示是否将try中指令添加边到catch的第一 条指令
    //第二个参数 是否所有的Labels 和 Gotos 从图中删除！
    public ControlFlowGraph2 (ReadMethod method, NodeFactory nodeFactory) {
        this(method, nodeFactory, false, false);
    }

    /**
     * Computes the <b>control flow graph</b> for one method.
     *
     * @param method the method for which the CFG is computed
     * @param nodeFactory the factory that creates the nodes of the CFG
     * @param addTryCatchEdges controls whether an edge should be inserted from each
     *                         instruction within a try block to the first instruction
     *                         in the catch block
     * @param excludeLabels if <code>true</code>, all Labels and goto instruction are excluded from the
     *                      CFG
     */
    public ControlFlowGraph2 (ReadMethod method, NodeFactory nodeFactory,
            boolean addTryCatchEdges, boolean excludeLabels) {
        this.method = method;
        // CFG 一个节点对应于Method 中的一条指令
        this.instructionNodes = new InstrNode[method.getInstructionNumberEnd() - method.getInstructionNumberStart()];
        for (Instruction instr: method.getInstructions()) {
        	// 前面只是简单生成各个指令对应的节点，并没有各个节点的前驱和后继信息！
            getInstrNode(instr, nodeFactory, excludeLabels); // getInstrNode 为了为每个指令节点生成前驱和后继信息！
        }
        // now add the edges from try blocks to catch/finally blocks
        if (addTryCatchEdges) {
            for (TryCatchBlock tcb: method.getTryCatchBlocks()) {
                LabelMarker handler = tcb.getHandler();
                Instruction nonLabel = excludeLabels ? followLabelsAndGotos(handler) : handler;
                assert nonLabel != null;
				InstrNode tcbHandler = getNode(nonLabel);
                for (Instruction inst = tcb.getStart(); inst != null && inst != tcb.getEnd(); inst = inst.getNext()) {
                    InstrNode instrNode = getNode(inst);
                    instrNode.addSuccessor(tcbHandler);
                    tcbHandler.addPredecessor(instrNode);
                }
            }
        }
    }

    /**
     * Returns the root of this CFG, which is just the Node corresponding to the
     * first instruction of this CFG's method, or null if the method contains no
     * instructions.
     *
     * If the CFG was created with <b>excludeLabels</b> and the first instruction is a label,
     * then the node for the first non-label instruction is returned.
     */
    public InstrNode getRootNode() {
    	// search for the first non-label node
        int idx = 0;
        if (idx < this.instructionNodes.length) {
            InstrNode instrNode = this.instructionNodes[idx];
            while (instrNode == null && idx < this.instructionNodes.length) {
                instrNode = this.instructionNodes[idx++];
            }
            return instrNode;
        }
        return null;
    }

    /**
     * Returns the method on which this CFG was built.
     *
     * @return the method on which this CFG was built.
     */
    public ReadMethod getMethod() {
        return this.method;
    }

    /**
     * Return the node of the CFG associated to the given {@link Instruction}.
     * If the instruction is not contained in the method that this CFG corresponds
     * to, then <code>null</code> is returned.
     *
     * If the CFG was created with <b>excludeLabels</b> and the given instruction is a label,
     * then the node for the next non-label instruction is returned.
     *
     * @param instr the {@link Instruction} for which the node is requested
     * @return the node corresponding to the given {@link Instruction}, or
     *         <code>null</code> if the instruction is not contained in the method of this CFG
     */
    public InstrNode getNode(Instruction instr) {
        int idx = instr.getIndex() - this.method.getInstructionNumberStart();
        if (idx >= 0 && idx < this.instructionNodes.length) {
            InstrNode instrNode = this.instructionNodes[idx];
            while (instrNode == null && idx < this.instructionNodes.length) {
                assert instr.getType() == InstructionType.LABEL;
                instrNode = this.instructionNodes[idx++];
            }
            return instrNode;
        }
        return null;
    }

    private Instruction followLabelsAndGotos(Instruction instr) {
    	Instruction nonLabel = instr;
    	while (nonLabel != null) {
    		if (nonLabel.getType() == InstructionType.LABEL) {
    			nonLabel = nonLabel.getNext();
    		} else if (nonLabel.getOpcode() == Opcodes.GOTO) {
				nonLabel = ((JumpInstruction2) nonLabel).getLabel().getNext();
    		} else
    			break;
    	}
    	return nonLabel;
    }

    protected InstrNode getInstrNode(Instruction instruction,
            NodeFactory nodeFactory, boolean excludeLabels) {
        int idx = instruction.getIndex() - this.method.getInstructionNumberStart();
        // instructionNodes 是方法CFG中所有节点，idx是指令偏移量
        InstrNode node = this.instructionNodes[idx];
        // 如果指令为Label和Goto并且 CFG中要求过滤，那么直接返回！
        if (node != null || (excludeLabels && (instruction.getType() == InstructionType.LABEL || instruction.getOpcode() == Opcodes.GOTO)))
            return node;
        
        InstrNode newNode = nodeFactory.createNode(this, instruction);
        this.instructionNodes[idx] = newNode;
        // getSuccessor(instruction) 返回该指令的所有后继指令！
        for (Instruction succ: getSuccessors(instruction)) {
        	Instruction nonLabel = excludeLabels ? followLabelsAndGotos(succ) : succ;
        	if (nonLabel == null)
        		continue;
            InstrNode succNode = getInstrNode(nonLabel, nodeFactory, excludeLabels);
            // 互相更新节点间的后继和前驱信息
            newNode.addSuccessor(succNode);
            succNode.addPredecessor(newNode);
        }
        return newNode;
    }

    // 返回一条指令的所有可能执行后继集合
    public Collection<Instruction> getSuccessors(Instruction instruction) {
        int opcode = instruction.getOpcode();
        // 按照index的大小返回下一条指令！， getnext仅仅是返回index+1的指令！
        Instruction nextInstruction = instruction.getNext();
        switch (instruction.getType()) {
        case JUMP:
            // GOTO and JSR are not conditional
        	// 无条件跳转只有一个后继！
            if (opcode == Opcodes.GOTO || opcode == Opcodes.JSR) {
                List<AbstractInstruction> instrs=this.method.instructions;
                Iterator<AbstractInstruction> iter=instrs.iterator();
                Instruction temp = null;
                while(iter.hasNext()){
                	temp=iter.next();
                	if(temp.getIndex()==((JumpInstruction2)instruction).getTarget())
                	break;
                }
                return Collections.singleton(temp);
            }
            assert nextInstruction != null;
            // 跳转指令后继包括两个，一个是它的传统nextInstruction, 另一个是它的label!
            List<AbstractInstruction> instrs=this.method.instructions;
            Iterator<AbstractInstruction> iter=instrs.iterator();
            Instruction temp = null;
            while(iter.hasNext()){
            	temp=iter.next();
            	if(temp.getIndex()==((JumpInstruction2)instruction).getTarget())
            	break;
            }
            return Arrays.asList(temp,nextInstruction);
            // switch 跳转型
        case LOOKUPSWITCH:
        {  
        	 LookupSwitchInstruction2 lsi = (LookupSwitchInstruction2) instruction;
        	 List<AbstractInstruction> instrs4=this.method.instructions;
        	 List<AbstractInstruction> instrs5=this.method.instructions;
        	 Iterator<AbstractInstruction> iter4=instrs4.iterator();
        	 Instruction temp2 = null;
        	 Instruction[] successors = new AbstractInstruction[lsi.getHandlers().size()+1];
        	 // find the default
        	 while(iter4.hasNext()){
        		 temp2=iter4.next();
        		 if(temp2.getIndex()==lsi.getDefaultHandler()){
        			 successors[0] =temp2;
        			 break;
        		 }
        	 }
        	 // find the handlers
        	 int index=0;
        	 for (Integer lm: lsi.getHandlers().values()){
        		 Iterator<AbstractInstruction> iter5=instrs5.iterator();
            	 while(iter5.hasNext()){
            		 temp2=iter5.next();
            		 if(temp2.getIndex()==lm){
            			 successors[index+1]=temp2;
            			 index++;
            			 break;
            		 }
            	 }
        	 }
        return Arrays.asList(successors);
        }
        // switch 跳转！
        case TABLESWITCH: 
        {
        	TableSwitchInstruction2 tsi = (TableSwitchInstruction2) instruction;
        	List<AbstractInstruction> instrs2=this.method.instructions;
        	List<AbstractInstruction> instrs3=this.method.instructions;
            Iterator<AbstractInstruction> iter2=instrs2.iterator();
            //Iterator<AbstractInstruction> iter3=instrs3.iterator();
            Instruction temp2 = null;
            Instruction[] successors=new AbstractInstruction[tsi.getHandlers().length+1];
            // get the default target
            while(iter2.hasNext()){
            	temp2=iter2.next();
            	if(tsi.getDefaultHandler()==temp2.getIndex())
            	{
            		successors[0]=temp2;
            		break;
            	}
            }
            // get the target from min to max! 
            for(int i=0;i<tsi.getHandlers().length;i++){
            	 Iterator<AbstractInstruction> iter3=instrs3.iterator();
            	 while(iter3.hasNext()){
            		 temp2=iter3.next();
            		 if(temp2.getIndex()==(tsi.getHandlers()[i])){
            			 successors[i+1]=temp2;
            			 break;
            		 }
            	 }
            }
            return Arrays.asList(successors);
        	/*
            TableSwitchInstruction tsi = (TableSwitchInstruction) instruction;
            Instruction[] successors = new AbstractInstruction[tsi.getHandlers().length+1];
            successors[0] = tsi.getDefaultHandler();
            System.arraycopy(tsi.getHandlers(), 0, successors, 1, tsi.getHandlers().length);
            return Arrays.asList(successors);*/
        }
        // 无参数指令需要特定处理return型的指令！此时他们的后继为空。其他类型返回传统的nextInstruction!
        case SIMPLE:
            switch (opcode) {
            case Opcodes.IRETURN: case Opcodes.LRETURN: case Opcodes.FRETURN:
            case Opcodes.DRETURN: case Opcodes.ARETURN: case Opcodes.RETURN:
                return Collections.emptySet();

            default:
                break;
            }
            break;
           // 加载指令需要特别处理ret 
        case VAR:
            if (opcode == Opcodes.RET) {
                List<JumpInstruction2> callingInstructions = getJsrInstructions((VarInstruction) instruction);
                Instruction[] successors = new AbstractInstruction[callingInstructions.size()];
                int i = 0;
                for (JumpInstruction2 instr: callingInstructions)
                    successors[i++] = instr.getNext();
                return Arrays.asList(successors);
            }
            break;
            // label型指令 为abnormalTermination时为空，否则为传统的nextInstruction!
        case LABEL:
            if (instruction == instruction.getMethod().getAbnormalTerminationLabel())
                return Collections.emptySet();
            break;
        default:
            break;
        }
        // 默认的是返回的后继是index+1的下一条指令！
        assert nextInstruction != null;
        return Collections.singleton(nextInstruction);
    }

    /**
     * Returns all <code>jsr</code> instructions that may end up in the given <code>ret</code> instructions.
     */
    private  List<JumpInstruction2> getJsrInstructions(VarInstruction retInstruction) {
        assert retInstruction.getOpcode() == Opcodes.RET;
        List<JumpInstruction2> list = new ArrayList<JumpInstruction2>();
        for (AbstractInstruction instr: retInstruction.getMethod().getInstructions()) {
            if (instr.getOpcode() == Opcodes.JSR) {
                Queue<Instruction> queue = new UniqueQueue<Instruction>();
                queue.add(((JumpInstruction2)instr).getLabel());
                while (!queue.isEmpty()) {
                    Instruction instr2 = queue.poll();
                    if (instr2.getOpcode() == Opcodes.RET) {
                        if (instr2 == retInstruction) {
                            list.add((JumpInstruction2)instr);
                        }
                        break;
                    }
                    queue.addAll(getSuccessors(instr));
                }
            }
        }

        return list;
    }

    @Override
	public List<InstrNode> getNodes() {
        if (this.nonNullPositions == null) {
            int numNonNull = 0;
            int[] newNonNullPositions = new int[this.instructionNodes.length];
            for (int i = 0; i < this.instructionNodes.length; ++i) {
                if (this.instructionNodes[i] != null) {
                    newNonNullPositions[numNonNull++] = i;
                }
            }
            this.nonNullPositions = new int[numNonNull];
            System.arraycopy(newNonNullPositions, 0, this.nonNullPositions, 0, numNonNull);

        }
        return new InstrList(this.instructionNodes, this.nonNullPositions);
    }

}
