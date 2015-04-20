/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.slicing
 *    Class:     Slicer
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/slicing/Slicer.java
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
package de.unisb.cs.st.javaslicer.slicing;

import static org.objectweb.asm.Opcodes.INVOKESTATIC;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.objectweb.asm.Opcodes;

import de.hammacher.util.maps.IntegerMap;
import de.unisb.cs.st.javaslicer.common.classRepresentation.AbstractInstructionInstance;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstance;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstanceFactory;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstanceInfo;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionType;
import de.unisb.cs.st.javaslicer.common.classRepresentation.LocalVariable;
import de.unisb.cs.st.javaslicer.common.classRepresentation.ReadMethod;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.AbstractInstruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.MethodInvocationInstruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.VarInstruction;
import de.unisb.cs.st.javaslicer.common.progress.ConsoleProgressMonitor;
import de.unisb.cs.st.javaslicer.common.progress.ProgressMonitor;
import de.unisb.cs.st.javaslicer.dependenceAnalysis.DataDependenceType;
import de.unisb.cs.st.javaslicer.dependenceAnalysis.DependencesExtractor;
import de.unisb.cs.st.javaslicer.dependenceAnalysis.DependencesVisitorAdapter;
import de.unisb.cs.st.javaslicer.dependenceAnalysis.VisitorCapability;
import de.unisb.cs.st.javaslicer.traceResult.PrintUniqueUntracedMethods;
import de.unisb.cs.st.javaslicer.traceResult.ThreadId;
import de.unisb.cs.st.javaslicer.traceResult.TraceResult;
import de.unisb.cs.st.javaslicer.traceResult.UntracedCallVisitor;
import de.unisb.cs.st.javaslicer.variables.Variable;

/**
 * This is the new slicer implementation, built on top of the {@link DependencesExtractor}.
 *
 * There still exists another implementation {@link DirectSlicer} which is more efficient and
 * should yield the same result. Nevertheless it is less maintained, so be warned.
 *
 * @author Clemens Hammacher
 */
public class Slicer {
   
	//extends inherent the father(AbstractInstructionInstance), implements the interface(AbstractInstruction)
    private static class SlicerInstance extends AbstractInstructionInstance {

        public boolean onDynamicSlice = false;

        // these variables are used to resolve which data dependences to follow:
        // 因为在 lastReader中维持这数据依赖的关系链，但是在切片中并不是所有的数据依赖我们都要visitor
        // 我们仅仅需要关注与切片相关的，就需要下面三个变量来表明From中是否有与切片相关的变量（From数据依赖To）
        public boolean allDataInteresting = false; 
        public Variable interestingVariable = null;
        public Set<Variable> moreInterestingVariables = null;

        public Set<SlicerInstance> predecessors; // only set on labels and GOTOs    其实没什么用！！！！

        public int criterionDistance;

        public SlicerInstance(AbstractInstruction instr, long occurenceNumber,
                int stackDepth, long instanceNr,
                InstructionInstanceInfo additionalInfo) {
            super(instr, occurenceNumber, stackDepth, instanceNr, additionalInfo);
            this.criterionDistance = Integer.MAX_VALUE;
        }

    }

    //slice instance extends Abstract instruction instance , which implements Instruction instance
    private static class SlicerInstanceFactory implements InstructionInstanceFactory<SlicerInstance> { //factory creates instance

        public static final SlicerInstanceFactory instance = new SlicerInstanceFactory();

        @Override
		public SlicerInstance createInstructionInstance(
                AbstractInstruction instruction, long occurenceNumber,
                int stackDepth, long instanceNr,
                InstructionInstanceInfo additionalInfo) {
            return new SlicerInstance(instruction, occurenceNumber, stackDepth, instanceNr, additionalInfo);
        }

    }
 // array list is dynamic array
    private  final TraceResult trace;
    private final List<ProgressMonitor> progressMonitors = new ArrayList<ProgressMonitor>(1); 
    private final List<SliceVisitor> sliceVisitors = new ArrayList<SliceVisitor>(1); // 在遍历动态切片的轨迹中的数据和控制依赖时来收集指令实例！
    private  List<UntracedCallVisitor> untracedCallVisitors = new ArrayList<UntracedCallVisitor>(1);

 
    
    public Slicer(TraceResult trace) {
        this.trace = trace;
    }

    public static void main(String[] args) throws InterruptedException {
        Options options = createOptions();
        CommandLineParser parser = new GnuParser();
        CommandLine cmdLine;

        try {
            cmdLine = parser.parse(options, args, true);
        } catch (ParseException e) {
            System.err.println("Error parsing the command line arguments: " + e.getMessage());
            return;
        }

        if (cmdLine.hasOption('h')) {
            printHelp(options, System.out);
            System.exit(0);
        }

        String[] additionalArgs = cmdLine.getArgs();
        if (additionalArgs.length != 2) {
            printHelp(options, System.err);
            System.exit(-1);
        } 
        // 参数只能有两个： 1. 是指定了文件的位置 2.给出了切片标准要求
        File traceFile = new File(additionalArgs[0]);
        String slicingCriterionString = additionalArgs[1];

        Long threadId = null;
        if (cmdLine.hasOption('t')) {  // the interesting thread id for slicing 
            try {
                threadId = Long.parseLong(cmdLine.getOptionValue('t'));
            } catch (NumberFormatException e) {
                System.err.println("Illegal thread id: " + cmdLine.getOptionValue('t'));
                System.exit(-1);
            }
        }

        TraceResult trace;
        try {
            trace = TraceResult.readFrom(traceFile);
        } catch (IOException e) {
            System.err.format("Could not read the trace file \"%s\": %s%n", traceFile, e);
            System.exit(-1);
            return;
        }

        List<SlicingCriterion> sc = null;  // a list contains the instruction's info corresponds to the slicing criterion
        //slicingCriterionString get from additionalArgs[1]
        try {
            sc = StaticSlicingCriterion.parseAll(slicingCriterionString, trace.getReadClasses());
        } catch (IllegalArgumentException e) {
            System.err.println("Error parsing slicing criterion: " + e.getMessage());
            System.exit(-1);
            return;
        }

        List<ThreadId> threads = trace.getThreads(); // the threads that generate the traces
        if (threads.size() == 0) {
            System.err.println("The trace file contains no tracing information.");
            System.exit(-1);
        }
       
        // threadID is used to mark the interesting thread
        ThreadId tracing = null;
        for (ThreadId t: threads) {
            if (threadId == null) {
                if ("main".equals(t.getThreadName()) && (tracing == null || t.getJavaThreadId() < tracing.getJavaThreadId()))
                    tracing = t;
            } else if (t.getJavaThreadId() == threadId.longValue()) {
                tracing = t;
            }
        }

        if (tracing == null) {
            System.err.println(threadId == null ? "Couldn't find the main thread."
                    : "The thread you specified was not found.");
            System.exit(-1);
            return;
        }

        long startTime = System.nanoTime();
        Slicer slicer = new Slicer(trace);
        if (cmdLine.hasOption("progress"))  // the parameter process indicates that we need to monitor the process of slicing
            slicer.addProgressMonitor(new ConsoleProgressMonitor());
        boolean multithreaded;
        if (cmdLine.hasOption("multithreaded")) {
            String multithreadedStr = cmdLine.getOptionValue("multithreaded");
            multithreaded = ("1".equals(multithreadedStr) || "true".equals(multithreadedStr));
        } else {
            multithreaded = Runtime.getRuntime().availableProcessors() > 1;
        }

        boolean warnUntracedMethods = cmdLine.hasOption("warn-untraced"); // give some warns when encounters untraced functions
  
        //sliceInstructionCollector implements the interface slice visitor, which travel the dependence graph
        SliceInstructionsCollector collector = new SliceInstructionsCollector();   // the collector is used to collect the instructions in the dependence graph according to the slice criterion. 
        slicer.addSliceVisitor(collector); 
        // zhushi by yhb
        
        if (warnUntracedMethods)
            slicer.addUntracedCallVisitor(new PrintUniqueUntracedMethods()); // the user need the untraced function info, so add untraced call visitor
            
        slicer.process(tracing, sc, multithreaded); //----------------------the key process of slicing!!!
        Set<InstructionInstance> slice = collector.getDynamicSlice(); // return the slice result from the collector
        long endTime = System.nanoTime();

        Instruction[] sliceArray = slice.toArray(new Instruction[slice.size()]); // convert the set to array
        Arrays.sort(sliceArray);  // in order to ensure the sequence of dynamic execution

        // show the slicing result
        System.out.println("The dynamic slice for criterion " + sc + ":");   
        for (Instruction insn: sliceArray) {
            System.out.format((Locale)null, "%s.%s:%d %s%n",
                    insn.getMethod().getReadClass().getName(),
                    insn.getMethod().getName(),
                    insn.getLineNumber(),
                    insn.toString());
        }
        System.out.format((Locale)null, "%nSlice consists of %d bytecode instructions.%n", sliceArray.length);
        System.out.format((Locale)null, "Computation took %.2f seconds.%n", 1e-9*(endTime-startTime));
    }

    public void addProgressMonitor(ProgressMonitor progressMonitor) {
        this.progressMonitors.add(progressMonitor);
    }

    public void addSliceVisitor(SliceVisitor sliceVisitor) {
        this.sliceVisitors.add(sliceVisitor);
    }

    
    public void addUntracedCallVisitor(UntracedCallVisitor untracedCallVisitor) {
        this.untracedCallVisitors.add(untracedCallVisitor);
    }

  
    
    
    
    
    
    //DependencesExtractor extracts the iterates backwards the trace, extract the dependence information
    //Visitor visit the edge in the result dependence information of DependenceExtractor
    public void process(ThreadId threadId, final List<SlicingCriterion> sc, boolean multithreaded) throws InterruptedException {
    	// 获取特定线程产生指令序列的DependenceExtractor, 它的方法中包含了切片的所有信息和切片的处理过程！
        DependencesExtractor<SlicerInstance> depExtractor = DependencesExtractor.forTrace(this.trace, SlicerInstanceFactory.instance); //trace is type of TraceResult!
        for (ProgressMonitor mon : this.progressMonitors)
            depExtractor.addProgressMonitor(mon); // ProcessMonitor用来对切片进度进行估计，依赖于labelsCrossed 的 数目

        // 下面定义了在切片过程中，我们感兴趣的边的访问！
        VisitorCapability[] capabilities = { VisitorCapability.CONTROL_DEPENDENCES, VisitorCapability.DATA_DEPENDENCES_READ_AFTER_WRITE, VisitorCapability.INSTRUCTION_EXECUTIONS,
                VisitorCapability.METHOD_ENTRY_LEAVE, VisitorCapability.CONTROL_DEPENDENCES }; 
        
        if (this.untracedCallVisitors.size() > 0)
        	capabilities[capabilities.length-1] = VisitorCapability.UNTRACED_METHOD_CALLS;
       //sliceVisitor which get informed about all nodes their dependences in dynamic slicing 
        final List<SliceVisitor> sliceVisitors0 = Slicer.this.sliceVisitors; 
        final List<UntracedCallVisitor> untracedCallVisitors0 = Slicer.this.untracedCallVisitors;
        // call this method before backward traversal 
  
        
        
        
        // --------------------------------------------------------REGISTER VISITOR-----------------------------------------------------------------
        //后面访问边的时候，是depExtractor.DependenceVisitorAdapter访问的！  
        depExtractor.registerVisitor(new DependencesVisitorAdapter<SlicerInstance>() {
        	// 这里大部分是第一个参数的定义，即DependenceVisitorAdapter的定义，包括各种依赖关系visit的动作
            private final List<SlicingCriterionInstance> slicingCritInst = instantiateSlicingCriteria(sc);
            @SuppressWarnings("unchecked")
           // InterestingLocalVariables表示再在切片过程中维持的LiveVariable集合，即感兴趣的变量集合！
            // 数组的下表对应于Stackdepth
            //数组中元素 使用一个MAP <int, Variable>， int是变量.getIndex!!, 表示在当前深度的方法中感兴趣的局部变量！
            // 成员默认设为null!
            private IntegerMap<Object>[] interestingLocalVariables = (IntegerMap<Object>[]) new IntegerMap<?>[0];
            // 存储的是深度为stackDepth时，当前正在处理实例匹配到的切片实例的OccurrenceNumber!--没有匹配为0
            // 没什么用！！！！
            private long[] critOccurenceNumbers = new long[2]; // 0 if not in a criterion
            // sliceVisitor 使用来收集动动态切片实例的！
            private final SliceVisitor[] sliceVisitorsArray = sliceVisitors0.toArray(new SliceVisitor[sliceVisitors0.size()]); 
           private final UntracedCallVisitor[] untracedCallsVisitorsArray = untracedCallVisitors0.toArray(new UntracedCallVisitor[untracedCallVisitors0.size()]);

            private ReadMethod enteredMethod; // 当前正在处理的方法

            // the number of sliceCriterions may be zero, 1 or many
            private List<SlicingCriterionInstance> instantiateSlicingCriteria(List<SlicingCriterion> criteria) {
            	System.out.println("entered ---------------------\n");
                if (criteria.isEmpty())
                    return Collections.emptyList();
                else if (criteria.size() == 1)
                {  System.out.println("instance of cri:  ");
                    System.out.println(criteria.get(0).getInstance().toString());
                    System.out.println(criteria.get(0).getInstance().getOccurenceNumber());
                	return Collections.singletonList(criteria.get(0).getInstance()); // getintance 就是new一个返回
                }
                else {
                    List<SlicingCriterionInstance> instances = new ArrayList<SlicingCriterionInstance>(criteria.size());
                    System.out.println("size of criteria:------------------------------------------  ");
                    System.out.print(criteria.size());
                    for (SlicingCriterion crit : criteria)
                        instances.add(crit.getInstance());
                    return instances;
                }
            }
     
            
            // the meaning of critOccurenceNumber?
            // very important to figure out the relation between critOccurrenceNum and stackDepth？以及LocalVariables与StackDepth 的关系？
            // Instance 与 Instruction 的 却别？ 
            @Override
            //----------------检查一条轨迹中的指令需要的动作！关键是先判定该指令是否对应于切片实例！
            public void visitInstructionExecution(SlicerInstance instance) {
                int stackDepth = instance.getStackDepth();
                
                if (this.critOccurenceNumbers.length <= stackDepth) {
                    long[] newCritOccurenceNumbers = new long[2*Math.max(this.critOccurenceNumbers.length, stackDepth)];
                   //arraycopy(被复制的数组, 从第几个元素开始复制, 要复制到的数组, 从第几个元素开始粘贴, 一共需要复制的元素个数);
                    System.arraycopy(this.critOccurenceNumbers, 0, newCritOccurenceNumbers, 0, this.critOccurenceNumbers.length);
                    this.critOccurenceNumbers = newCritOccurenceNumbers;
                }
                Instruction instruction = instance.getInstruction();
                for (SlicingCriterionInstance crit : this.slicingCritInst) {
                    if (crit.matches(instance)) { // 当前指令对应于一条切片的标准
                    	System.out.print("matched !!-----------------\n");
                    	System.out.println(instance.getInstruction().getLineNumber());
                    	System.out.print("line----index");
                    	System.out.println(instance.getInstruction().getIndex());
                        this.critOccurenceNumbers[stackDepth] = crit.getOccurenceNumber(); // how to do if there are two Criterions in the same stack Depth?
                        assert this.critOccurenceNumbers[stackDepth] > 0;
                        // for each criterion, there are three cases:
                        //  - track all data read by the instruction
                        //  - track a given set of local variables
                        //  - track the control dependences of this instruction
                        // in the second case, the instruction itself is not added to the dynamic slice
                        instance.allDataInteresting = crit.matchAllData();
                        if (!instance.allDataInteresting && crit.hasLocalVariables()) { // 第二种情况
                            if (this.interestingLocalVariables.length <= stackDepth) {  // local interesting variable why compare to stack Length?
                                @SuppressWarnings("unchecked")
                                IntegerMap<Object>[] newInterestingLocalVariables =
                                        (IntegerMap<Object>[]) new IntegerMap<?>[Math.max(stackDepth+1, this.interestingLocalVariables.length*3/2)];
                                System.arraycopy(this.interestingLocalVariables, 0, newInterestingLocalVariables, 0, this.interestingLocalVariables.length);
                                this.interestingLocalVariables = newInterestingLocalVariables;
                            }
                            List<LocalVariable> localVariables = crit.getLocalVariables();
                            if (this.interestingLocalVariables[stackDepth] == null)
                                this.interestingLocalVariables[stackDepth] = new IntegerMap<Object>(localVariables.size()*4/3+1);
                            for (LocalVariable i : localVariables)
                            	// 为何此时i.getIndex对应的Object是null?-------------------------------
                                this.interestingLocalVariables[stackDepth].put(i.getIndex(), null); 
                        } else {  // 第一种或者第三种情况
                            if (instruction.getType() != InstructionType.LABEL)  //第一种或者第三种情况(排除LABEL)需要将实例加入到切片结果中！
                                for (SliceVisitor vis : this.sliceVisitorsArray) 
                                    vis.visitMatchedInstance(instance);   // sliceVisitorr来收集切片实例！
                            instance.onDynamicSlice = true;  // not the second case, need to put into the slice
                            instance.criterionDistance = 0;   // because instance match the Criterion, so set it to 0
                        }
                    } else if (this.critOccurenceNumbers[stackDepth] != 0) {
                        this.critOccurenceNumbers[stackDepth] = 0;
                    }
                }
               //约束条件表明当前判定的是数据依赖关系的判定！
                if (this.interestingLocalVariables.length > stackDepth &&
                        this.interestingLocalVariables[stackDepth] != null) {
                    switch (instruction.getOpcode()) {
                        case Opcodes.ISTORE:
                        case Opcodes.ASTORE:
                        case Opcodes.LSTORE:
                        case Opcodes.FSTORE:
                        case Opcodes.DSTORE:
                            VarInstruction varInsn = (VarInstruction) instruction;
                            if (this.interestingLocalVariables[stackDepth].containsKey(varInsn.getLocalVarIndex())) {
                                this.interestingLocalVariables[stackDepth].remove(varInsn.getLocalVarIndex()); //写了敏感变量，那么该敏感变量要移除
                                if (this.interestingLocalVariables[stackDepth].isEmpty())
                                    this.interestingLocalVariables[stackDepth] = null;
                                for (SliceVisitor vis : this.sliceVisitorsArray)  // sliceVisitor收集切片实例
                                    vis.visitMatchedInstance(instance); 
                                instance.onDynamicSlice = true;
                                // and we want to know where the data comes from...
                                instance.allDataInteresting = true;
                                instance.criterionDistance = 0;
                            }
                            break;
                        case Opcodes.INVOKEINTERFACE:
                        case Opcodes.INVOKESPECIAL:
                        case Opcodes.INVOKESTATIC:
                        case Opcodes.INVOKEVIRTUAL:
                            if (this.enteredMethod != null) {
                                MethodInvocationInstruction mtdInvInsn = (MethodInvocationInstruction) instruction;
                                int paramCount = instruction.getOpcode() == INVOKESTATIC ? 0 : 1;
                                for (int param = mtdInvInsn.getParameterCount()-1; param >= 0; --param)
                                    paramCount += mtdInvInsn.parameterIsLong(param) ? 2 : 1;
                                //entered method- the method that calls this instruction
                                boolean enteredMethodMatches = this.enteredMethod.getName().equals(mtdInvInsn.getInvokedMethodName())
                                    && this.enteredMethod.getDesc().equals(mtdInvInsn.getInvokedMethodDesc());
                                if (enteredMethodMatches) {
                                    boolean localVarsMatched = false;
                                    for (int varNr = 0; varNr < paramCount; ++varNr) {
                                        if (this.interestingLocalVariables[stackDepth].containsKey(varNr)) {
                                            this.interestingLocalVariables[stackDepth].remove(varNr); // 敏感变量对应于方法调用参数，将敏感变量移除。方法调用加入到slice中
                                            if (this.interestingLocalVariables[stackDepth].isEmpty())
                                                this.interestingLocalVariables[stackDepth] = null;  //因为InterestingLocalVariables 初始数组大小为0,是由于上一一步的MatchCri才加入内容的。
                                            localVarsMatched = true;
                                            instance.onDynamicSlice = true;
                                            // and we want to know where the data comes from...
                                            // TODO
                                            instance.allDataInteresting = true;
                                            instance.criterionDistance = 0;
                                        }
                                    }
                                    if (localVarsMatched)
                                        for (SliceVisitor vis : this.sliceVisitorsArray)   // sliceVisitor收集切片实例
                                            vis.visitMatchedInstance(instance); 
                                }
                            }
                    }
                }
                this.enteredMethod = null;
                // enteredMethod 只有逆向扫描到methodentry时才赋值，逆向扫描到methodInvoke后，将其赋值为null!
            }
          
            // in the control dependent graph, from points to to, but to controls the execution of from
            // first of all from must onDynamicSlice
            //criterion distance is the distance from instruction to criterion
            //predecessor is only set on labels or Goto! ---why?
            // update the criterion distance and predecessor
            @Override
            // A 是B 的 predecessor 表示B控制A的执行，B再程序里面可能有多个后继，但是为什么label要设置呢？。
            public void visitControlDependence(SlicerInstance from,
                    SlicerInstance to) {
                if (from.onDynamicSlice) { 
                    Instruction insn = to.getInstruction();
                    // labelMarker 和 Goto L1类型的指令才有predecessors!!????
                    if (insn.getType() == InstructionType.LABEL || insn.getOpcode() == Opcodes.GOTO) {  //LABEL stands for labelMARKER, which is a marker for jump targets
                    	if (to.predecessors == null)
                			to.predecessors = Collections.singleton(from); //means which to execute next in the program 
                    	else {
                    		if (to.predecessors.size() == 1) // size为1的时候就要扩容来添加，非一的时候已经增加了扩容选项了！
	                			to.predecessors = new HashSet<SlicerInstance>(to.predecessors);
	                    	to.predecessors.add(from);
                    	}
                    	if (from.criterionDistance < to.criterionDistance)
                    		to.criterionDistance = from.criterionDistance;  //to 本身不会出现再结果中，属于要被过滤的，所以本身不计入distance!!!
                    } // to有多个predecessors的时候，from就不可能再有多个predecessors，所以分这两种情况！
                    else if (from.predecessors != null) {
                    	assert (!from.predecessors.isEmpty());
                    	for (SlicerInstance pred : from.predecessors) {
	                        int distance = pred.criterionDistance+1; // 因为本身是Goto 和 label 这些指令会在最终结果中过滤掉，所以前面没有加1，但是此时要加1
	                        //加1是对应的实例to！
	                        delegateControlSliceDependence(pred, to, distance); // for the liveSet update，并且用sliceVisitor来收集敏感字节吗
	                    	if (distance < to.criterionDistance)
	                    		to.criterionDistance = distance;   // 寻找最短的值复制给to的cirdistance!
                    	}
                    } else {
                        int distance = from.criterionDistance+1;
                        delegateControlSliceDependence(from, to, distance); // for the liveSet update，并且用sliceVisitor来收集敏感字节吗
                    	if (distance < to.criterionDistance)
                    		to.criterionDistance = distance;
                    }
                    to.onDynamicSlice = true;
                }
            }

			private void delegateControlSliceDependence(SlicerInstance from,
					SlicerInstance to, int distance) {

				for (SliceVisitor vis : this.sliceVisitorsArray)    //收集控制依赖相关的切片实例！
				    vis.visitSliceDependence(from, to, null, distance);  

                // since "to" controls the execution of "from", we want to track all data dependences of "to"
                // to find out why it took this decision
                // exception: method invocations; here we only want to track why the method was executed,
                // but not the data that it consumed
				// important to check that "from" comes from inside the method which is called by "from"  ----------------------meaning?
				
				// 如果to不是方法调用，那么to的所有变量都要跟踪，相反则只需要判定为什么这个方法调用被执行！
				boolean calledMethodDependence = false;
				if (to.getInstruction().getType() == InstructionType.METHODINVOCATION) {
					MethodInvocationInstruction mtdInv = (MethodInvocationInstruction) to.getInstruction();
					ReadMethod calledMethod = from.getInstruction().getMethod();  //the method that calls "from"
					if (mtdInv.getInvokedMethodName().equals(calledMethod.getName()) &&  //getInvokedMN returns the name of  Method
							mtdInv.getInvokedMethodDesc().equals(calledMethod.getDesc())) {  
						calledMethodDependence = true;
					}
				}
                if (!calledMethodDependence) {
                    to.allDataInteresting = true; // if to is not a method invocation instruction ,the we need to track all data dependence of "to"
                }
			}
 
			// from depends on to
			//? represent any type!
			// update corresponding information when travel data dependence edges
			// interestingVariable represent the first one in fromVar, moreInterestingVarialbe represent the others.
			// 主要是数据依赖的liveSet更新情况操作
            @Override
            public void visitDataDependence(SlicerInstance from,
                    SlicerInstance to, Collection<? extends Variable> fromVars,
                    Variable toVar, DataDependenceType type)
                    throws InterruptedException {
                assert type == DataDependenceType.READ_AFTER_WRITE;
   // 即使存在数据依赖，也要判定这些数据依赖是不是与切片相关的liveSet中关心的！！
                if (from.onDynamicSlice && // from must definitively be on the dynamic slice
                        (from.allDataInteresting || // and either we want to track all data dependencies
                            (from.interestingVariable != null && ( // or (if the interestingVariable is set) ...
                                from.interestingVariable.equals(toVar) || // the interestingVariable must be the one we are just visiting
                                (from.moreInterestingVariables != null && from.moreInterestingVariables.contains(toVar)))))) { // or it must be in the set of more variables
                    Instruction insn = to.getInstruction();
                    assert insn.getType() != InstructionType.LABEL;
                    int distance = from.criterionDistance+1;
                	if (distance < to.criterionDistance)
                		to.criterionDistance = distance;
                    for (SliceVisitor vis : this.sliceVisitorsArray)    // 收集数据相关的切片实例！
                        vis.visitSliceDependence(from, to, toVar, distance);  
                    if (!fromVars.isEmpty()) {  
                    	// interesting 和 moreinteresing 记录了一条指令中涉及到切片的敏感数据依赖！
                    	// 数据相关事，关于敏感变量的划分，第一个定位interestingVariable, 剩余的定位more interestingVariable!
                        Iterator<? extends Variable> varIt = fromVars.iterator();
                        assert varIt.hasNext() : "Iterator of a non-empty collection should have at least one element";
                        Variable first = varIt.next();
                        if (to.interestingVariable == null || to.interestingVariable.equals(first)) {
                            to.interestingVariable = first;
                           first = varIt.hasNext() ? varIt.next() : null;
                        }
                        if (first != null) {
                            if (to.moreInterestingVariables == null)
                                to.moreInterestingVariables = new HashSet<Variable>(8);
                            to.moreInterestingVariables.add(first);
                            while (varIt.hasNext())
                                to.moreInterestingVariables.add(varIt.next());
                        }
                    }
                    to.onDynamicSlice = true;
                }
            }
           

            @Override
            public void visitMethodLeave(ReadMethod method, int stackDepth)
                    throws InterruptedException {
            // 刚进入到一个方法调用中，将局部敏感变量全部设为空！
                if (this.interestingLocalVariables.length > stackDepth &&
                        this.interestingLocalVariables[stackDepth] != null) {
                    this.interestingLocalVariables[stackDepth] = null; // 进入一个新的方法中，原来的要清空！
                }
            }

            @Override
            public void visitMethodEntry(ReadMethod method, int stackDepth)
                    throws InterruptedException {
                if (this.interestingLocalVariables.length > stackDepth &&
                        this.interestingLocalVariables[stackDepth] != null) {
                    this.enteredMethod = method;
                    this.interestingLocalVariables[stackDepth] = null; // 退出一个方法时也要清空！
                }
            }

            @Override
            public void visitUntracedMethodCall(SlicerInstance instrInstance)
                    throws InterruptedException {
                for (UntracedCallVisitor vis : this.untracedCallsVisitorsArray)
                    vis.visitUntracedMethodCall(instrInstance);
            }

        }, capabilities);  // end of register visitor

        depExtractor.processBackwardTrace(threadId, multithreaded);
    }

    @SuppressWarnings("static-access")
    private static Options createOptions() {
        Options options = new Options();
        options.addOption(OptionBuilder.isRequired(false).withArgName("threadid").hasArg(true).
            withDescription("thread id to select for slicing (default: main thread)").withLongOpt("threadid").create('t'));
        options.addOption(OptionBuilder.isRequired(false).hasArg(false).
            withDescription("show progress while computing the dynamic slice").withLongOpt("progress").create('p'));
        options.addOption(OptionBuilder.isRequired(false).hasArg(false).
            withDescription("print this help and exit").withLongOpt("help").create('h'));
        options.addOption(OptionBuilder.isRequired(false).hasArg(true).withArgName("value").
            withDescription("process the trace in a multithreaded way (pass 'true' or '1' to enable, anything else to disable). Default is true iff we have more than one processor").
            withLongOpt("multithreaded").create('m'));
        options.addOption(OptionBuilder.isRequired(false).hasArg(false).
            withDescription("warn once for each method which is called but not traced").withLongOpt("warn-untraced").create('u'));
        return options;
    }

    private static void printHelp(Options options, PrintStream out) {
        out.println("Usage: " + Slicer.class.getSimpleName() + " [<options>] <file> <slicing criterion>");
        out.println("where <file> is the input trace file");
        out.println("      <slicing criterion> has the form <loc>[(<occ>)]:<var>[,<loc>[(<occ>)]:<var>]*");
        out.println("      <options> may be one or more of");
        HelpFormatter formatter = new HelpFormatter();
        PrintWriter pw = new PrintWriter(out, true);
        formatter.printOptions(pw, 120, options, 5, 3);
    }

}
