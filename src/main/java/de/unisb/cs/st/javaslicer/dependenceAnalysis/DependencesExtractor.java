/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.dependenceAnalysis
 *    Class:     DependencesExtractor
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/dependenceAnalysis/DependencesExtractor.java
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
package de.unisb.cs.st.javaslicer.dependenceAnalysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import org.objectweb.asm.Opcodes;

import de.hammacher.util.collections.BlockwiseSynchronizedBuffer;
import de.hammacher.util.maps.IntegerMap;
import de.unisb.cs.st.javaslicer.common.classRepresentation.AbstractInstructionInstance;
import de.unisb.cs.st.javaslicer.common.classRepresentation.AbstractInstructionInstanceFactory;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstance;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstanceFactory;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionType;
import de.unisb.cs.st.javaslicer.common.classRepresentation.ReadMethod;
import de.unisb.cs.st.javaslicer.common.classRepresentation.instructions.LabelMarker;
import de.unisb.cs.st.javaslicer.common.exceptions.TracerException;
import de.unisb.cs.st.javaslicer.common.progress.ProgressInformationProvider;
import de.unisb.cs.st.javaslicer.common.progress.ProgressMonitor;
import de.unisb.cs.st.javaslicer.controlflowanalysis.ControlFlowAnalyser;
import de.unisb.cs.st.javaslicer.instructionSimulation.AdditionalDataDependence;
import de.unisb.cs.st.javaslicer.instructionSimulation.DynamicInformation;
import de.unisb.cs.st.javaslicer.instructionSimulation.SimulationEnvironment;
import de.unisb.cs.st.javaslicer.instructionSimulation.Simulator;
import de.unisb.cs.st.javaslicer.traceResult.BackwardTraceIterator;
import de.unisb.cs.st.javaslicer.traceResult.ThreadId;
import de.unisb.cs.st.javaslicer.traceResult.TraceResult;
import de.unisb.cs.st.javaslicer.variables.ArrayElement;
import de.unisb.cs.st.javaslicer.variables.LocalVariable;
import de.unisb.cs.st.javaslicer.variables.ObjectField;
import de.unisb.cs.st.javaslicer.variables.StackEntry;
import de.unisb.cs.st.javaslicer.variables.Variable;


/**
 * This class iterates (backwards) through the execution trace and visits
 * all dynamic data and control dependences, and other events like method entries
 * or exits.
 *
 * @author Clemens Hammacher
 */
// 注意便利的是动态产生的轨迹，访问轨迹上的所有的动态数据和控制依赖，并访问其他选项例如方法的进入和退出！
public class DependencesExtractor<InstanceType extends InstructionInstance> {

    private final TraceResult trace;
    
    private final Simulator<InstanceType> simulator;

    private final Set<DependencesVisitorAdapter<? super InstanceType>> dataDependenceVisitorsReadAfterWrite = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> dataDependenceVisitorsWriteAfterRead = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> controlDependenceVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> instructionVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> pendingDataDependenceVisitorsReadAfterWrite = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> pendingDataDependenceVisitorsWriteAfterRead = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> pendingControlDependenceVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> methodEntryLeaveVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> untracedMethodsVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();
    private final Set<DependencesVisitorAdapter<? super InstanceType>> objectCreationVisitors = new HashSet<DependencesVisitorAdapter<? super InstanceType>>();

    private final InstructionInstanceFactory<? extends InstanceType> instanceFactory;
    private final Set<ProgressMonitor> progressMonitors = new HashSet<ProgressMonitor>(2);


    /**
     * Constructs a {@link DependencesExtractor} for a given trace, using the default
     * {@link AbstractInstructionInstanceFactory}.
     *
     * @param trace the trace that this DependencesExtracter should traverse
     * @return a new {@link DependencesExtractor}
     * @see #DependencesExtractor(TraceResult, InstructionInstanceFactory)
     */
    
    
    
    public static DependencesExtractor<InstructionInstance> forTrace(TraceResult trace) {
        InstructionInstanceFactory<? extends InstructionInstance> factory = new AbstractInstructionInstanceFactory();
        return new DependencesExtractor<InstructionInstance>(trace, factory);
    }

    /**
     * @see #DependencesExtractor(TraceResult, InstructionInstanceFactory)
     * @return a new {@link DependencesExtractor} for the given trace, using the given instance factory
     */
    public static <InstanceType extends InstructionInstance> DependencesExtractor<InstanceType> forTrace(
            TraceResult trace, InstructionInstanceFactory<? extends InstanceType> instanceFactory) {
        return new DependencesExtractor<InstanceType>(trace, instanceFactory);
    }

    /**
     * Constructs a {@link DependencesExtractor} for a given trace and a user-definable instance factory.
     *
     * NOTE: Please use the static methods to construct a DependencesExtractor.
     *
     * @param trace the trace that this DependencesExtracter should traverse
     * @param instanceFactory the factory to create the instruction instances
     */
    private DependencesExtractor(TraceResult trace, InstructionInstanceFactory<? extends InstanceType> instanceFactory) {
        this.trace = trace;
        this.simulator = new Simulator<InstanceType>(trace);
        this.instanceFactory = instanceFactory;
    }

    /**
     * Registers a {@link DependencesVisitor} with this {@link DependencesExtractor}.
     * This method should only be called before {@link #processBackwardTrace(long)}.
     *
     * During traversal, calles to this method and {@link #unregisterVisitor(DependencesVisitor)}
     * have no influence to this traversal any more.
     *
     * @param visitor the {@link DependencesVisitor} to register
     * @param capabilities the capabilities of the visitor (determines which
     *                     methods are called on the visitor)
     * @return <code>true</code> if the visitor was registered with any new capability
     */
    // capabilities 决定了visit时visitor调用那个方法！   为DependenceExtractor 注册感兴趣的DependenceVisitor !
    // DependenceVisitor 访问动态轨迹中一个特定的依赖，并更新相关敏感信息 
    public boolean registerVisitor(DependencesVisitorAdapter<? super InstanceType> visitor, VisitorCapability... capabilities) {
        boolean change = false; // 有个新加的依赖注册判定成功，就 为真 ，所有 为 或操作子 ！
        for (VisitorCapability cap: capabilities) {
            switch (cap) {
            case DATA_DEPENDENCES_ALL:
                change |= this.dataDependenceVisitorsReadAfterWrite.add(visitor);
                change |= this.dataDependenceVisitorsWriteAfterRead.add(visitor);
                break;
            case DATA_DEPENDENCES_READ_AFTER_WRITE:
                change |= this.dataDependenceVisitorsReadAfterWrite.add(visitor);
                System.out.println("RAW\n");
                break;
            case DATA_DEPENDENCES_WRITE_AFTER_READ:
                change |= this.dataDependenceVisitorsWriteAfterRead.add(visitor);
               System.out.println("WAR\n");
                break;
            case CONTROL_DEPENDENCES:
                change |= this.controlDependenceVisitors.add(visitor);
                System.out.println("ControlDep\n");
                break;
            case INSTRUCTION_EXECUTIONS:
                change |= this.instructionVisitors.add(visitor);
                System.out.println("INSTR exec\n");
                break;
            case PENDING_CONTROL_DEPENDENCES:
                change |= this.pendingControlDependenceVisitors.add(visitor);
                break;
            case PENDING_DATA_DEPENDENCES_ALL:
                change |= this.pendingDataDependenceVisitorsReadAfterWrite.add(visitor);
                change |= this.pendingDataDependenceVisitorsWriteAfterRead.add(visitor);
                break;
            case PENDING_DATA_DEPENDENCES_READ_AFTER_WRITE:
                change |= this.pendingDataDependenceVisitorsReadAfterWrite.add(visitor);
                break;
            case PENDING_DATA_DEPENDENCES_WRITE_AFTER_READ:
                change |= this.pendingDataDependenceVisitorsWriteAfterRead.add(visitor);
                break;
            case METHOD_ENTRY_LEAVE:
                change |= this.methodEntryLeaveVisitors.add(visitor);
                break;
            case UNTRACED_METHOD_CALLS:
                change |= this.untracedMethodsVisitors.add(visitor);
                break;
            case OBJECT_CREATION:
                change |= this.objectCreationVisitors.add(visitor);
                break;
            }
        }
        return change;
    }

    /**
     * Unregisters a {@link DependencesVisitor} with all registered capabilities.
     * This method should only be called before {@link #processBackwardTrace(long)}.
     *
     * During traversal, calles to this method and {@link #registerVisitor(DependencesVisitor, VisitorCapability...)}
     * have no influence to this traversal any more.
     *
     * @param visitor the {@link DependencesVisitor} to unregister
     * @return <code>true</code> if the visitor was registered with any capabilities
     */
    public boolean unregisterVisitor(DependencesVisitor<InstanceType> visitor) {
        boolean change = false;
        change |= this.dataDependenceVisitorsReadAfterWrite.remove(visitor);
        change |= this.dataDependenceVisitorsWriteAfterRead.remove(visitor);
        change |= this.controlDependenceVisitors.remove(visitor);
        change |= this.instructionVisitors.remove(visitor);
        change |= this.pendingDataDependenceVisitorsReadAfterWrite.remove(visitor);
        change |= this.pendingDataDependenceVisitorsWriteAfterRead.remove(visitor);
        change |= this.pendingControlDependenceVisitors.remove(visitor);
        change |= this.methodEntryLeaveVisitors.remove(visitor);
        change |= this.objectCreationVisitors.remove(visitor);
        return change;
    }

    /**
     * Go backwards through the execution trace of the given threadId and extract
     * all dependences. {@link DependencesVisitor}s should have been added before
     * by calling {@link #registerVisitor(DependencesVisitor, VisitorCapability...)}.
     *
     * If you know the exact {@link ThreadId} of the thread to process, you should
     * use {@link #processBackwardTrace(ThreadId)} instead, since a java thread id
     * does not have to be unique.
     *
     * @param javaThreadId identifies the thread whose trace should be analyzed
     * @throws InterruptedException if the thread was interrupted during traversal
     * @throws IllegalArgumentException if the trace contains no thread with this id
     */
    //javaThreadID指出了那一个进程的轨迹需要分析依赖关系, 由DependenceExtractor来调用该逆向扫描方法
    public void processBackwardTrace(long javaThreadId) throws InterruptedException {
        ThreadId id = this.trace.getThreadId(javaThreadId);
        if (id == null)
            throw new IllegalArgumentException("No such thread id");
        processBackwardTrace(id);
    }
    

    /**
     * Calls {@link #processBackwardTrace(ThreadId, boolean)} with multithreaded == false
     *
     * @throws InterruptedException if the thread was interrupted during traversal
     * @see #processBackwardTrace(ThreadId, boolean)
     */
    public void processBackwardTrace(ThreadId threadId) throws InterruptedException {
        processBackwardTrace(threadId, false);
    }

   

    /**
     * Go backwards through the execution trace of the given threadId and extract
     * all dependences. {@link DependencesVisitor}s should have been added before
     * by calling {@link #registerVisitor(DependencesVisitor, VisitorCapability...)}.
     *
     * @param threadId identifies the thread whose trace should be analyzed
     * @param multithreaded use an extra thread to traverse the trace
     * @throws InterruptedException if the thread was interrupted during traversal
     * @throws IllegalArgumentException if the trace contains no thread with this id
     */
    // backward 扫描threadId产生的trace，获取所有的感兴趣动态依赖关系！multithreaded 标识是否采用多线程来处理！
    // 在backward中，遇到依赖处理，就调用注册的DependenceVisitor 来处理这样的关系！
    static int aa=1;
	static int ww=1;
    
    public void processBackwardTrace(ThreadId threadId, boolean multithreaded) throws InterruptedException {
    
    	// 构造一个面向特定线程产生指令的逆向遍历iterator, 其中threadId用来获取特定的ThreadTraceResult
        final BackwardTraceIterator<InstanceType> backwardInsnItr =
        		//null 标记的为filter参数，功能是在扫描过程中过滤掉特定指令，默认的filter为过滤labels 和addtionalLabels!
            this.trace.getBackwardIterator(threadId, null, this.instanceFactory);

        if (backwardInsnItr == null)
            throw new IllegalArgumentException("No such thread");

        // store the current set of visitors of each capability in an array for better
        // performance and faster empty-check (null reference if empty)
      //  System.out.println("size of RAW visitor :");
     //   System.out.print(this.dataDependenceVisitorsReadAfterWrite.size());
        
        final DependencesVisitor<? super InstanceType>[] dataDependenceVisitorsReadAfterWrite0 = this.dataDependenceVisitorsReadAfterWrite.isEmpty()
            ? null : this.dataDependenceVisitorsReadAfterWrite.toArray(
                newDependencesVisitorArray(this.dataDependenceVisitorsReadAfterWrite.size()));
   //     System.out.println("RAW array size:  ");
   //     System.out.print(this.dataDependenceVisitorsReadAfterWrite.size());
        final DependencesVisitor<? super InstanceType>[] dataDependenceVisitorsWriteAfterRead0 = this.dataDependenceVisitorsWriteAfterRead.isEmpty()
            ? null : this.dataDependenceVisitorsWriteAfterRead.toArray(
                newDependencesVisitorArray(this.dataDependenceVisitorsWriteAfterRead.size()));
        final DependencesVisitor<? super InstanceType>[] controlDependenceVisitors0 = this.controlDependenceVisitors.isEmpty()
            ? null : this.controlDependenceVisitors.toArray(
                newDependencesVisitorArray(this.controlDependenceVisitors.size()));
        System.out.println("Control array size:  ");
        System.out.print(this.controlDependenceVisitors.size());
        final DependencesVisitor<? super InstanceType>[] instructionVisitors0 = this.instructionVisitors.isEmpty()
            ? null : this.instructionVisitors.toArray(
                newDependencesVisitorArray(this.instructionVisitors.size()));
        final DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsReadAfterWrite0 = this.pendingDataDependenceVisitorsReadAfterWrite.isEmpty()
            ? null : this.pendingDataDependenceVisitorsReadAfterWrite.toArray(
                newDependencesVisitorArray(this.pendingDataDependenceVisitorsReadAfterWrite.size()));
        final DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsWriteAfterRead0 = this.pendingDataDependenceVisitorsWriteAfterRead.isEmpty()
            ? null : this.pendingDataDependenceVisitorsWriteAfterRead.toArray(
                newDependencesVisitorArray(this.pendingDataDependenceVisitorsWriteAfterRead.size()));
        final DependencesVisitor<? super InstanceType>[] pendingControlDependenceVisitors0 = this.pendingControlDependenceVisitors.isEmpty()
            ? null : this.pendingControlDependenceVisitors.toArray(
                newDependencesVisitorArray(this.pendingControlDependenceVisitors.size()));
        final DependencesVisitor<? super InstanceType>[] methodEntryLeaveVisitors0 = this.methodEntryLeaveVisitors.isEmpty()
            ? null : this.methodEntryLeaveVisitors.toArray(
                newDependencesVisitorArray(this.methodEntryLeaveVisitors.size()));
        final DependencesVisitor<? super InstanceType>[] objectCreationVisitors0 = this.objectCreationVisitors.isEmpty()
            ? null : this.objectCreationVisitors.toArray(
                newDependencesVisitorArray(this.objectCreationVisitors.size()));

        @SuppressWarnings("unchecked")
        DependencesVisitor<? super InstanceType>[] allVisitors = union(
            dataDependenceVisitorsReadAfterWrite0,
            dataDependenceVisitorsWriteAfterRead0,
            controlDependenceVisitors0,
            instructionVisitors0,
            pendingDataDependenceVisitorsReadAfterWrite0,
            pendingDataDependenceVisitorsWriteAfterRead0,
            pendingControlDependenceVisitors0,
            methodEntryLeaveVisitors0,
            objectCreationVisitors0);
      
         // controlDependence 是一个由Set<instrucion>类型组成的 Integermap,  
        // Int 型的key为指令的index!
        // 确定了是存储了在一个方法中所有控制依赖于instr的指令集合！
        // 如果直接获取没有，那么就在CFG上计算！
        IntegerMap<Set<Instruction>> controlDependences = new IntegerMap<Set<Instruction>>();

        // 非多线程处理的话 ，instanceIterator 和 processInfoProv 都是前面构造的BackwardInstrInterator!
        Iterator<InstanceType> instanceIterator;  
        ProgressInformationProvider progressInfoProv;
        Thread iteratorThread = null;
        final AtomicReference<Throwable> iteratorException = new AtomicReference<Throwable>(null);
        if (multithreaded) {
            final AtomicLong percentPerInstance = this.progressMonitors.isEmpty()
                ? null
                : new AtomicLong(Double.doubleToLongBits(0)); // this AtomicLong holds a double value!!

            final BlockwiseSynchronizedBuffer<InstanceType> buffer = new BlockwiseSynchronizedBuffer<InstanceType>(1<<16, 1<<20);
            final InstanceType firstInstance = backwardInsnItr.hasNext() ? backwardInsnItr.next() : null;
            iteratorThread = new Thread("Trace iterator") {
                @Override
                public void run() {
                    try {
                        int num = 0;
                        while (backwardInsnItr.hasNext()) {
                            buffer.put(backwardInsnItr.next());
                            if ((++num & ((1<<16)-1)) == 0 && percentPerInstance != null) {
                                double percentPerInstance0 = backwardInsnItr.getPercentageDone() / num;
                                percentPerInstance.set(Double.doubleToLongBits(percentPerInstance0));
                            }
                        }
                    } catch (Throwable t) {
                        iteratorException.compareAndSet(null, t);
                    } finally {
                        try {
                            buffer.put(firstInstance); // to signal that this is the end of the trace
                            buffer.flush();
                        } catch (InterruptedException e) {
                            iteratorException.compareAndSet(null, e);
                        }
                    }
                }
            };
            iteratorThread.start();
            final AtomicLong numInstancesSeen = percentPerInstance == null
                ? null
                : new AtomicLong(0);
            instanceIterator = new Iterator<InstanceType>() {

                private InstanceType next = firstInstance;

                @Override
				public boolean hasNext() {
                    if (this.next == null) {
                        while (true) {
                            try {
                                this.next = buffer.take();
                                if (this.next == firstInstance) {
                                    this.next = null;
                                }
                                break;
                            } catch (InterruptedException e) {
                                // this.next stays null
                                assert this.next == null;
                                Thread.currentThread().interrupt();
                            }
                        }
                    }
                    return this.next != null;
                }

                @Override
				public InstanceType next() {
                    if (!hasNext())
                        throw new NoSuchElementException();
                    InstanceType ret = this.next;
                    this.next = null;
                    if (numInstancesSeen != null)
                        numInstancesSeen.incrementAndGet();
                    return ret;
                }
                @Override
				public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
            progressInfoProv = percentPerInstance == null
                ? null
                : new ProgressInformationProvider() {
                    @Override
					public double getPercentageDone() {
                        return Double.longBitsToDouble(percentPerInstance.get()) *
                                numInstancesSeen.get();
                    }
                };
        } else {
            instanceIterator = backwardInsnItr;
            progressInfoProv = backwardInsnItr;
        }

        // the lastWriter is needed for WAR data dependences
        Map<Variable, InstanceType> lastWriter = new HashMap<Variable, InstanceType>();
        
        
        
        // lastReaders are needed for RAW data dependences
        // 我们关心的是RAW 所以只需要关心lastReaders  Map<Variables, list<InstanceInstr>>
        // 存储的是依赖特定变量的所有指令，例如指令A ： a=b+c; 则 <b,A> <c,A> 都是lastReader的成员!
        Map<Variable, List<InstanceType>> lastReaders = new HashMap<Variable, List<InstanceType>>();

        /*
        HashSet<Long> createdObjects = new HashSet<Long>();
        HashSet<Long> seenObjects = new HashSet<Long>();
        */

        InstanceType instance = null;
        Instruction instruction = null;

        for (ProgressMonitor mon : this.progressMonitors)
            mon.start(progressInfoProv);
      //try catch 执行try 中的代码，如果try中发生异常则执行catch 中的代码！finally 一定会执行！
        try {
            // 用来标记逆向扫描过程中遇到的方法调用，从0开始依次增加！
        	// 只有进入方法调用的时候NextFrameNr才++！
        	// frame下标为被调用方法对应的stackDepth，值为该方法被扫描到的排序Nr！
            long nextFrameNr = 0;
            int stackDepth = 0;
           //返回lastStackMethods 中的所有方法！
            List<ReadMethod> initialStackMethods = backwardInsnItr.getInitialStackMethods();

            int allocStack = initialStackMethods.size() + 1;
            // 二进制数熟的话, 其实就是一句话, 返回最高位为1, 其它位为0的数
            allocStack = Integer.highestOneBit(allocStack)*2;

            @SuppressWarnings("unchecked")
            InstanceType[] atCatchBlockStart = (InstanceType[])(new InstructionInstance[allocStack]);
            boolean[] throwsException = new boolean[allocStack];
            boolean[] interruptedControlFlow = new boolean[allocStack];
            /**
             * <code>true</code> iff this frame was aborted abnormally (NOT by a RETURN
             * instruction)
             */
            // 一个frame对应于当前栈内压入的一个方法！
            boolean[] abnormalTermination = new boolean[allocStack];
            /**
             * is set to true if the methods entry label has been passed
             */
            // finished 表示该方法的entrylabel 已经处理，即整个方法已经逆向处理完!
            // 也不用看，DerectSlicing 用！
            boolean[] finished = new boolean[allocStack];
            
            
            int[] opStack = new int[allocStack];
            int[] minOpStack = new int[allocStack];
            long[] frames = new long[allocStack];
            Instruction[] lastInstruction = new Instruction[allocStack];
            
            @SuppressWarnings("unchecked")
            // InteresingInstance 存储在一个StackDepth下与切片相关的控制依赖指令！！！
            // 方法调用的判定通过两重：1.visitInstrexec ---data dependence 2.Control Dependence的判定用interestingInstance[r+1]
            HashSet<InstanceType>[] interestingInstances = (HashSet<InstanceType>[]) new HashSet<?>[allocStack];
           
            
            // 全局性质的局部变量信息和栈元素信息！！，用于数据依赖判定中的 def 和 use信息的提取！！
            StackEntry[][] cachedStackEntries = new StackEntry[allocStack][];
            LocalVariable[][] cachedLocalVariables = new LocalVariable[allocStack][];
            
            //method数组的大小为栈的深度，描述的是Frame栈深度下所对应的的方法。
            ReadMethod[] method = new ReadMethod[allocStack];

            
          // -------------------正常情况下，由于lastStackMethods为0，所以initialStackMethods也为0，所以该循环不执行
			for (ReadMethod method0: initialStackMethods) {
				System.out.println("initialStackMethods  -------------------------visiting \n");
            	++stackDepth; //stackDepth 初始为0，所以有多少个lastStackMethod StackDepth 就有多深！
            	method[stackDepth] = method0;
            	interruptedControlFlow[stackDepth] = true;
            	frames[stackDepth] = nextFrameNr++; // 深度1，nextFramNr0; 2-1; 3-2.。。//初始情况
                if (methodEntryLeaveVisitors0 != null)
                    for (DependencesVisitor<? super InstanceType> vis: methodEntryLeaveVisitors0)
                        vis.visitMethodLeave(method0, stackDepth); 
            }
			
          // 因为stackDepth 是从1开始的
			for (int i = 1; i < allocStack; ++i) {
            	interestingInstances[i] = new HashSet<InstanceType>(); // 深度为i时感兴趣的切片实例存放
            	cachedStackEntries[i] = new StackEntry[8]; // 深度为i 时存放的栈操作元素信息！
            	cachedLocalVariables[i] = new LocalVariable[8]; // 深度为i 存放的临时变量信息！
			}
			
			SimulationEnvironment simEnv = new SimulationEnvironment(frames, opStack, minOpStack,
				cachedStackEntries, cachedLocalVariables, throwsException, lastInstruction, method, interruptedControlFlow);
       
		   // 通过 Iterator 来逆向取出下一条指令！	
			// while循环中你想不断的取next指令来获取下一条要分析的指令！
            while (instanceIterator.hasNext()) {
            	
                instance = instanceIterator.next();
                if(instance.getInstruction().getMethod().getName().contains("main"))
                	System.out.println(instance.toString());
                
                instruction = instance.getInstruction();
              	if(ww==1){
            		System.out.println("initial value of allock: ");
            		System.out.print(allocStack);
            		System.out.println("\n");
            		System.out.println("initial value of stackDepth: ");
            		System.out.print(instance.getStackDepth());
            		System.out.println(instance.toString());
            		ww--;
            	}
              // backward traverse 中，instanceNr从0开始
                if ((instance.getInstanceNr() & ((1<<16)-1)) == 0 && Thread.interrupted())
                    throw new InterruptedException();

                int newStackDepth = instance.getStackDepth();
                assert newStackDepth > 0;

                simEnv.removedMethod = null;
                boolean reenter = false;
         
                
                //表示进入了新的方法，或者退出了方法，或者重新进入了某个方法！
                // finished[stackDepeth]=true  表明之前已经访问过当前深度的方法！！！
                if (newStackDepth != stackDepth || (reenter = finished[stackDepth] || method[stackDepth] != instruction.getMethod())) {
                	// 表示当前的指令在序列中在新调用了的方法中！
                    if (newStackDepth >= stackDepth) {
                        // in all steps, the stackDepth can change by at most 1 (except for the very first instruction)
                        assert newStackDepth == stackDepth+1 || stackDepth == 0 || reenter;
                        if (newStackDepth >= atCatchBlockStart.length)  {
                        	int oldLen = atCatchBlockStart.length;
                        	int newLen = oldLen == 0 ? 8 : 2*oldLen;
                            atCatchBlockStart = Arrays.copyOf(atCatchBlockStart, newLen);
                            throwsException = Arrays.copyOf(throwsException, newLen);
                            interruptedControlFlow = Arrays.copyOf(interruptedControlFlow, newLen);
                            abnormalTermination = Arrays.copyOf(abnormalTermination, newLen);
                            finished = Arrays.copyOf(finished, newLen);
                            opStack = Arrays.copyOf(opStack, newLen);
                            minOpStack = Arrays.copyOf(minOpStack, newLen);
                            frames = Arrays.copyOf(frames, newLen);
                            interestingInstances = Arrays.copyOf(interestingInstances, newLen);
                            lastInstruction = Arrays.copyOf(lastInstruction, newLen);
                            cachedStackEntries = Arrays.copyOf(cachedStackEntries, newLen);
                            cachedLocalVariables = Arrays.copyOf(cachedLocalVariables, newLen);
                            method = Arrays.copyOf(method, newLen);
                            for (int i = oldLen; i < newLen; ++i) {
                            	interestingInstances[i] = new HashSet<InstanceType>();
                            	cachedStackEntries[i] = new StackEntry[8];
                            	cachedLocalVariables[i] = new LocalVariable[8];
                            }
                			simEnv = new SimulationEnvironment(frames, opStack, minOpStack,
                				cachedStackEntries, cachedLocalVariables, throwsException, lastInstruction, method, interruptedControlFlow);
                        }
                        frames[newStackDepth] = nextFrameNr++;
                        ReadMethod oldMethod = method[newStackDepth];
                        method[newStackDepth] = instruction.getMethod();
                 
                        if (methodEntryLeaveVisitors0 != null) {
                            for (DependencesVisitor<? super InstanceType> vis: methodEntryLeaveVisitors0) {
                            	if (reenter) //******************************
                            	{
                            		vis.visitMethodEntry(oldMethod, newStackDepth);
                            		if(oldMethod.getName().contains("fyhb")){
                            		System.out.println(oldMethod.getName());
                            		System.out.println("IN reenter enty visiting *****************************************************************  \n");}
                            	}
                                vis.visitMethodLeave(method[newStackDepth], newStackDepth);
                            }
                        }

                        if (reenter) {
                        	cleanUpExecutionFrame(simEnv, stackDepth, lastReaders, lastWriter,
                            	pendingDataDependenceVisitorsWriteAfterRead0, pendingDataDependenceVisitorsReadAfterWrite0,
                            	dataDependenceVisitorsWriteAfterRead0, dataDependenceVisitorsReadAfterWrite0);
                        }

                        atCatchBlockStart[newStackDepth] = null;
                        if (instruction == method[newStackDepth].getAbnormalTerminationLabel()) {
                            throwsException[newStackDepth] = interruptedControlFlow[newStackDepth] = abnormalTermination[newStackDepth] = true;
                            interruptedControlFlow[stackDepth] = true;
                        } else {
	                        throwsException[newStackDepth] = interruptedControlFlow[newStackDepth] = abnormalTermination[newStackDepth] = false;
                        }
                        finished[newStackDepth] = false;
                        // 扫描进入一个方法内部，初始化opStack[stackDepth]=0
                        // 刚进入到一个方法内部，此时操作数栈是空的，所以Opstack[stackDepth]=0!
                        opStack[newStackDepth] = 0;
                        minOpStack[newStackDepth] = 0;
                        // 此时进入了一个新的方法，故它的控制感兴趣指令实例集合为空
                        interestingInstances[newStackDepth].clear();
                        if (cachedLocalVariables[newStackDepth].length > 128){
                        	cachedLocalVariables[newStackDepth] = new LocalVariable[8];
                        	System.out.println("LV>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>128\n");
                        }
                        else
                        	// 刚进入一个新的方法，此时要将缓存的局部变量信息清空！，获取的时候可以从对应的Method中拿！
                        	Arrays.fill(cachedLocalVariables[newStackDepth], null);
                        if (cachedStackEntries[newStackDepth].length > 128){
                        	cachedStackEntries[newStackDepth] = new StackEntry[8];
                        	System.out.println("ST>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>128\n");
                        }
                        else
                        	Arrays.fill(cachedStackEntries[newStackDepth], null);

                    } else {
                        assert newStackDepth == stackDepth-1;
                        if (methodEntryLeaveVisitors0 != null) {
                            for (DependencesVisitor<? super InstanceType> vis: methodEntryLeaveVisitors0) {
                            	// 当前是a.b.c 中的c的invoke被访问，所以要visit c的entry! 这个条件与上一个的关键不同是stackDepth!=newstackDepth!
                                vis.visitMethodEntry(method[stackDepth], stackDepth);
                            }
                        }
                        //访问完了一个method的标记是visitMethodEntry， 即newStackDepth=stackDepth-1
                        simEnv.removedMethod = method[stackDepth];
                    }
                }
                
                // 更新stackDepth!!
                stackDepth = newStackDepth;
           
                // this.removedMethod==null 表明该方法没有扫描它的entryLabel，即没有进入方法进行扫描
                if (simEnv.removedMethod == null &&
                		(this.untracedMethodsVisitors != null) &&
                		(instruction.getType() == InstructionType.METHODINVOCATION)) {
                    for (DependencesVisitor<? super InstanceType> vis: this.untracedMethodsVisitors)
                        vis.visitUntracedMethodCall(instance);
                }

                if (instruction == instruction.getMethod().getMethodEntryLabel()) // 当前处理的指令是methodEntryLabel 那么表示再当前stackDepth的方法已经finished
                    finished[stackDepth] = true;
                
                lastInstruction[stackDepth] = instruction; 

                if (atCatchBlockStart[stackDepth] != null)
                	throwsException[stackDepth] = true;
          // DynamicInfo 主要包括动态切片中用到的def use createObj信息
                DynamicInformation dynInfo = this.simulator.simulateInstruction(instance, simEnv);

                if (instructionVisitors0 != null)  // 每一条被分析的指令都要被instructionVisitor 来visit
                    for (DependencesVisitor<? super InstanceType> vis: instructionVisitors0)
                        vis.visitInstructionExecution(instance);

                // the computation of control dependences only has to be performed
                // if there are any controlDependenceVisitors
                // 630-------703 -----------------------------------------是控制依赖链的逆向更新扫描过程！！！
                if (controlDependenceVisitors0 != null) {
                	// 只有访问了一个方法的entryLabel，removedMethod才会非null,所以此时指令对应于方法调用指令
                	// 该方法调用指令是否再切片中取决与它调用的方法中是否存在切片敏感指令
                	// interesting[stackDepth] 表明在该深度下与切片相关敏感指令集合！
                    if (simEnv.removedMethod != null &&
                            !interestingInstances[stackDepth + 1].isEmpty()) {
                        // ok, we have a control dependence since the method was called by (or for) this instruction
                        // checking if this is the instr. that directly called the method is impossible
                        for (InstanceType depend : interestingInstances[stackDepth + 1]) {
                            for (DependencesVisitor<? super InstanceType> vis: controlDependenceVisitors0) {
                                vis.visitControlDependence(depend, instance);
                            }
                        }
                        interestingInstances[stackDepth].add(instance); // 该方法调用指令加入到当前的深度的敏感指令中！
                    }
                    // controlDependence 是一个由Set<instrucion>类型组成的 Integermap, 
                    // 确定了是存储了在该方法中所有控制依赖于instr的指令集合！
                    // 如果直接获取没有，那么就在CFG上计算！
                    Set<Instruction> instrControlDependences = controlDependences.get(instruction.getIndex());
                    if (instrControlDependences == null) {
                    	// 在CFG上计算该指令的控制指令集合！
                    	// 计算该方法调用指令调用的方法的控制依赖关系，结果存放在controlDependence 的Map中
                        computeControlDependences(instruction.getMethod(), controlDependences);
                        instrControlDependences = controlDependences.get(instruction.getIndex());
                        assert instrControlDependences != null;
                    }
                    boolean isExceptionsThrowingInstruction = throwsException[stackDepth] &&
                        (instruction.getType() != InstructionType.LABEL || !((LabelMarker)instruction).isAdditionalLabel()) &&
                        (instruction.getOpcode() != Opcodes.GOTO);
                    // assert: every ATHROW must be an exception throwing instance
                    assert (instruction.getOpcode() != Opcodes.ATHROW || isExceptionsThrowingInstruction);
                    // get all interesting instructions, that are dependent on the current one
                    
                    // interestingInstance[stackDepth] 是再动态切片中该方法中逆向扫描到现在所产生的动态切片实例，包含控制的和数据的！
                    // InstrcontrolDependence是该该方法下，该指令实例对应指令的所有控制依赖指令！
                    // 求交集得出的是该指令在动态下面的控制依赖指令！
                    Set<InstanceType> dependantInterestingInstances = getInstanceIntersection(instrControlDependences, interestingInstances[stackDepth]);
                    
                    
                    // 下面可以不用看！！！
                    if (isExceptionsThrowingInstruction) {
                        throwsException[stackDepth] = false;
                        // in this case, we have an additional control dependence from the catching to
                        // the throwing instruction, and a data dependence on the thrown instruction
                        for (int i = stackDepth; i > 0; --i) {
                            if (atCatchBlockStart[i] != null) {
                                if (interestingInstances[i].contains(atCatchBlockStart[i])) {
                                    if (dependantInterestingInstances.isEmpty())
                                        dependantInterestingInstances = Collections.singleton(atCatchBlockStart[i]);
                                    else
                                        dependantInterestingInstances.add(atCatchBlockStart[i]);
                                }
                                atCatchBlockStart[i] = null;

                                // data dependence:
                                // (the stack height has already been decremented when entering the catch block)
                                Variable definedException = simEnv.getOpStackEntry(i, opStack[i]);
                                dynInfo = AdditionalDataDependence.annotate(dynInfo, definedException, dynInfo.getUsedVariables());

                                break;
                            }
                        }
                    }
                    
                    if (!dependantInterestingInstances.isEmpty()) {
                        for (InstanceType depend: dependantInterestingInstances) {
                            for (DependencesVisitor<? super InstanceType> vis: controlDependenceVisitors0) {
                                vis.visitControlDependence(depend, instance);  // 关键的控制依赖指令实例，depend依赖于instance!
                            }
                        }
                    	interestingInstances[stackDepth].removeAll(dependantInterestingInstances);
                    }
                    interestingInstances[stackDepth].add(instance);  // b,c依赖于a，将a加入，删除b,c! 
                }
                // TODO check this:
                
                
                
                if (pendingControlDependenceVisitors0 != null) {
                	interestingInstances[stackDepth].add(instance);
                    for (DependencesVisitor<? super InstanceType> vis: pendingControlDependenceVisitors0)
                        vis.visitPendingControlDependence(instance); 
                    System.out.println("visiting pending Control Dependence!");
                }

                
                
                // 从现在到 ， 是数据依赖链的更新逆向扫描过程！
                Collection<? extends Variable> definedVariables = dynInfo.getDefinedVariables(); // 获取定义的变量！
              // 当前这条指令定义了变量！
                if (!definedVariables.isEmpty()) {
                    /*
                    for (Variable definedVariable: dynInfo.getDefinedVariables()) {
                        if (definedVariable instanceof ObjectField) {
                            seenObjects.add(((ObjectField)definedVariable).getObjectId());
                            assert !createdObjects.contains(((ObjectField)definedVariable).getObjectId());
                        }
                        if (definedVariable instanceof ArrayElement) {
                            seenObjects.add(((ArrayElement)definedVariable).getArrayId());
                            assert !createdObjects.contains(((ArrayElement)definedVariable).getArrayId());
                        }
                    }
                    */
                    if (dataDependenceVisitorsReadAfterWrite0 != null
                            || dataDependenceVisitorsWriteAfterRead0 != null
                            || pendingDataDependenceVisitorsWriteAfterRead0 != null) {
                        for (Variable definedVariable: definedVariables) {
                            if (!(definedVariable instanceof StackEntry)) {
                                // we ignore WAR dependences over the stack!
                                if (pendingDataDependenceVisitorsWriteAfterRead0 != null) {
                                    // for each defined variable, we have a pending WAR dependence
                                    // if the lastWriter is not null, we first discard old pending dependences
                                    InstanceType varLastWriter = lastWriter.put(definedVariable, instance);
                                    for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsWriteAfterRead0) {
                                        if (varLastWriter != null)
                                            vis.discardPendingDataDependence(varLastWriter, definedVariable, DataDependenceType.WRITE_AFTER_READ);
                                        vis.visitPendingDataDependence(instance, definedVariable, DataDependenceType.WRITE_AFTER_READ);
                                    }
                                // otherwise, if there are WAR visitors, we only update the lastWriter
                                } else if (dataDependenceVisitorsWriteAfterRead0 != null) {
                                    lastWriter.put(definedVariable, instance);
                                }
                            }
                            // if we have RAW visitors, we need to analyze the lastReaders
                            // 注意，readers中的所有指令都是数据依赖于instance的！
                            // A =b+c ; B=A; 那么 usedVariable 就是b,c definde Variable 就是A
                            // lastReaders 是一个Map < variables,List<Instructions>>  
                            // lastReaders  是每个变量所对应的实例范围，即读该变量能读到当前值的范围！
                            if (dataDependenceVisitorsReadAfterWrite0 != null
                                    || pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                            	// remove会返回definedVariable 所对应的指令集合！
                            	// remove返回的是definedVariable 对应的readers, 即指令读了definedVariable
                                List<InstanceType> readers = lastReaders.remove(definedVariable); // 定义了，那么数据依赖过程中该变量就需要remove
                                // 即后面有对该变量的读！
                                if (readers != null) {
                                	// usedVaraiable 表示该变量的定义所用到的变量集合！
                                    Collection<? extends Variable> usedVariables = dataDependenceVisitorsReadAfterWrite0 != null
                                        ? dynInfo.getUsedVariables(definedVariable)  // 取出与当前定义变量相关的使用变量集合！
                                        : null;
                                    for (InstanceType reader: readers) {
                                        if (dataDependenceVisitorsReadAfterWrite0 != null) {
                                            for (DependencesVisitor<? super InstanceType> vis: dataDependenceVisitorsReadAfterWrite0)
                                                vis.visitDataDependence(reader, instance, usedVariables, definedVariable, DataDependenceType.READ_AFTER_WRITE);
                                        }
                                        if (pendingDataDependenceVisitorsReadAfterWrite0 != null)
                                            for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsReadAfterWrite0)
                                                vis.discardPendingDataDependence(reader, definedVariable, DataDependenceType.READ_AFTER_WRITE);
                                    }
                                }
                            }
                        }
                    }
                }

                Collection<? extends Variable> usedVariables = dynInfo.getUsedVariables();
                // 获取当前实例的使用变量集合！
                if (!usedVariables.isEmpty()) {
                    /*
                    for (Variable usedVariable: dynInfo.getUsedVariables()) {
                        if (usedVariable instanceof ObjectField) {
                            seenObjects.add(((ObjectField)usedVariable).getObjectId());
                            assert !createdObjects.contains(((ObjectField)usedVariable).getObjectId());
                        }
                        if (usedVariable instanceof ArrayElement) {
                            seenObjects.add(((ArrayElement)usedVariable).getArrayId());
                            assert !createdObjects.contains(((ArrayElement)usedVariable).getArrayId());
                        }
                    }
                    */

                    if (dataDependenceVisitorsWriteAfterRead0 != null ||
                            dataDependenceVisitorsReadAfterWrite0 != null ||
                            pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                        for (Variable usedVariable: usedVariables) {
                            // if we have WAR visitors, we inform them about a new dependence
                            if (dataDependenceVisitorsWriteAfterRead0 != null && !(usedVariable instanceof StackEntry)) {
                                InstanceType lastWriterInst = lastWriter.get(usedVariable);

                                // avoid self-loops in the DDG (e.g. for IINC, which reads and writes to the same variable)
                                if (lastWriterInst != null && lastWriterInst != instance) {
                                    for (DependencesVisitor<? super InstanceType> vis: dataDependenceVisitorsWriteAfterRead0)
                                        vis.visitDataDependence(lastWriterInst, instance, null, usedVariable, DataDependenceType.WRITE_AFTER_READ);
                                }
                            }

                            // for RAW visitors, update the lastReaders
                            // 更新lastReaders

                            if (dataDependenceVisitorsReadAfterWrite0 != null
                                    || pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                                List<InstanceType> readers = lastReaders.get(usedVariable);
                                if (readers == null) {
                                    readers = new ArrayList<InstanceType>(4);
                                    lastReaders.put(usedVariable, readers);
                                }
                                readers.add(instance); 
                                // 因为instance指令依赖于b,c, 即A=b+c.所以，b,c对应的readers 应该添加上instance!!
                                // for each used variable, we have a pending RAW dependence
                                if (pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                                    for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsReadAfterWrite0)
                                        vis.visitPendingDataDependence(instance, usedVariable, DataDependenceType.READ_AFTER_WRITE);
                                }
                            }
                        }
                    }
                }
 
                
                
                // 因为getCreatedObjects返回的是HashMap<long, Variable>不支持iterator,所以.entrySet()返回这个
                // HashMap的一个集合视图，可以进行iterator访问！
                // object e 是一个collection 类型，扩展了variable 
                // 这种指令为A=new object O;
                // 当前指令创建了对象！！！
                for (Entry<Long, Collection<? extends Variable>> e: dynInfo.getCreatedObjects().entrySet()) {
                    /*
                    boolean added = createdObjects.add(e.getKey());
                    assert added;
                    */

                    for (Variable var: e.getValue()) {
                        assert var instanceof ObjectField || var instanceof ArrayElement;
                        // clean up lastWriter if we have any WAR visitors
                        if (pendingDataDependenceVisitorsWriteAfterRead0 != null) {
                            InstanceType inst;
                            if ((inst = lastWriter.remove(var)) != null)
                                for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsWriteAfterRead0)
                                    vis.discardPendingDataDependence(inst, var, DataDependenceType.WRITE_AFTER_READ);
                        } else if (dataDependenceVisitorsWriteAfterRead0 != null)
                            lastWriter.remove(var);
                        
                        
                        
                        // clean up lastReaders if we have any RAW visitors  
                        // 对象e中的变量，可能在后面被使用，所以增加这样的判定！
                        // instlist 中的指令就对应于e中变量var的readers！
                        if (dataDependenceVisitorsReadAfterWrite0 != null || pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                            List<InstanceType> instList;
                            if ((instList = lastReaders.remove(var)) != null) {  // 表明有对该对象变量的读！，需要visitDataDependence!
                                if (dataDependenceVisitorsReadAfterWrite0 != null)
                                    for (DependencesVisitor<? super InstanceType> vis: dataDependenceVisitorsReadAfterWrite0)
                                        for (InstanceType instrInst: instList)
                                            vis.visitDataDependence(instrInst, instance, Collections.<Variable>emptySet(), var, DataDependenceType.READ_AFTER_WRITE);
                                if (pendingDataDependenceVisitorsReadAfterWrite0 != null)
                                    for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsReadAfterWrite0)
                                        for (InstanceType instrInst: instList)
                                         vis.discardPendingDataDependence(instrInst, var, DataDependenceType.READ_AFTER_WRITE);
                            }
                        }
                    }
                    if (objectCreationVisitors0 != null)
                    {
                        for (DependencesVisitor<? super InstanceType> vis: objectCreationVisitors0)
                            vis.visitObjectCreation(e.getKey(), instance);
                      System.out.println("visit object creation!********************************");
                    }
                }

                if (dynInfo.isCatchBlock()) {
                    atCatchBlockStart[stackDepth] = instance;
                    interruptedControlFlow[stackDepth] = true;
                } else if (atCatchBlockStart[stackDepth] != null) {
                    atCatchBlockStart[stackDepth] = null;
                }

                if (simEnv.removedMethod != null) {
                    cleanUpExecutionFrame(simEnv, stackDepth+1, lastReaders, lastWriter,
                        pendingDataDependenceVisitorsWriteAfterRead0, pendingDataDependenceVisitorsReadAfterWrite0,
                        dataDependenceVisitorsWriteAfterRead0, dataDependenceVisitorsReadAfterWrite0);
                }

                /*
                if (instance.getInstanceNr() % 1000000 == 0) {
                    for (Variable var: lastReaders.keySet()) {
                        if (var instanceof ObjectField) {
                            assert seenObjects.contains(((ObjectField)var).getObjectId());
                            assert !createdObjects.contains(((ObjectField)var).getObjectId());
                        }
                        if (var instanceof ArrayElement) {
                            assert seenObjects.contains(((ArrayElement)var).getArrayId());
                            assert !createdObjects.contains(((ArrayElement)var).getArrayId());
                        }
                        if (var instanceof StackEntry)
                            assert frames.contains(((StackEntry)var).getFrame());
                        if (var instanceof LocalVariable) {
                            assert frames.contains(((LocalVariable)var).getFrame());
                        }
                    }
                    for (Variable var: lastWriter.keySet()) {
                        if (var instanceof ObjectField) {
                            assert seenObjects.contains(((ObjectField)var).getObjectId());
                            assert !createdObjects.contains(((ObjectField)var).getObjectId());
                        }
                        if (var instanceof ArrayElement) {
                            assert seenObjects.contains(((ArrayElement)var).getArrayId());
                            assert !createdObjects.contains(((ArrayElement)var).getArrayId());
                        }
                        // we do not store the last writer of a stack entry
                        assert !(var instanceof StackEntry);
                        if (var instanceof LocalVariable) {
                            assert frames.contains(((LocalVariable)var).getFrame());
                        }
                    }
                }
                */
            }
            Throwable t = iteratorException.get();
            if (t != null) {
                if (t instanceof RuntimeException)
                    throw (RuntimeException)t;
                if (t instanceof Error)
                    throw (Error)t;
                if (t instanceof InterruptedException)
                    throw (InterruptedException)t;
                throw new TracerException(
                    "Iterator should not throw anything but RuntimeExceptions", t);
            }

            if (Thread.interrupted())
                throw new InterruptedException();

            cleanUpMaps(lastWriter, lastReaders, pendingDataDependenceVisitorsWriteAfterRead0, pendingDataDependenceVisitorsReadAfterWrite0);

            for (DependencesVisitor<? super InstanceType> vis: allVisitors)
                vis.visitEnd(instance == null ? 0 : instance.getInstanceNr());

            if (Thread.interrupted())
                throw new InterruptedException();
        } //--------------------------------------------------------the end of try!
        catch (InterruptedException e) {
            for (DependencesVisitor<? super InstanceType> vis: allVisitors)
                vis.interrupted();
            throw e;
        } finally {
            if (iteratorThread != null)
                iteratorThread.interrupt();
            for (ProgressMonitor mon : this.progressMonitors)
                mon.end();
        }
    }
    // end of ProcessBackwardIterator!!!---------------------------------------------------------------------------------------------------------------

	private DependencesVisitor<? super InstanceType>[] union(
            DependencesVisitor<? super InstanceType>[] ... visitors) {
        Set<DependencesVisitor<? super InstanceType>> allVisitors =
            new HashSet<DependencesVisitor<? super InstanceType>>();
        for (DependencesVisitor<? super InstanceType>[] viss : visitors)
            if (viss != null)
                for (DependencesVisitor<? super InstanceType> vis : viss)
                    allVisitors.add(vis);
        return allVisitors.toArray(newDependencesVisitorArray(allVisitors.size()));
    }

    @SuppressWarnings("unchecked")
    private DependencesVisitor<? super InstanceType>[] newDependencesVisitorArray(int size) {
        return (DependencesVisitor<? super InstanceType>[]) new DependencesVisitor<?>[size];
    }

    private void cleanUpExecutionFrame(SimulationEnvironment simEnv, int stackDepth,
            Map<Variable, List<InstanceType>> lastReaders,
            Map<Variable, InstanceType> lastWriter,
            DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsWriteAfterRead0,
            DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsReadAfterWrite0,
            DependencesVisitor<? super InstanceType>[] dataDependenceVisitorsWriteAfterRead0,
            DependencesVisitor<? super InstanceType>[] dataDependenceVisitorsReadAfterWrite0) throws InterruptedException {
        for (Variable var: simEnv.getAllVariables(stackDepth)) {
            // lastWriter does not contain stack entries
            if (!(var instanceof StackEntry)) {
                if (pendingDataDependenceVisitorsWriteAfterRead0 != null) {
                    InstanceType inst = lastWriter.remove(var);
                    if (inst != null)
                        for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsWriteAfterRead0)
                            vis.discardPendingDataDependence(inst, var, DataDependenceType.WRITE_AFTER_READ);
                } else if (dataDependenceVisitorsWriteAfterRead0 != null)
                    lastWriter.remove(var);
            }
            if (pendingDataDependenceVisitorsReadAfterWrite0 != null) {
                List<InstanceType> instList = lastReaders.remove(var);
                if (instList != null)
                    for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsReadAfterWrite0)
                        for (InstanceType instrInst: instList)
                            vis.discardPendingDataDependence(instrInst, var, DataDependenceType.READ_AFTER_WRITE);
            } else if (dataDependenceVisitorsReadAfterWrite0 != null)
                lastReaders.remove(var);
        }
    }

    private void cleanUpMaps(Map<Variable, InstanceType> lastWriter,
            Map<Variable, List<InstanceType>> lastReaders,
            DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsWriteAfterRead0,
            DependencesVisitor<? super InstanceType>[] pendingDataDependenceVisitorsReadAfterWrite0) throws InterruptedException {
        if (pendingDataDependenceVisitorsWriteAfterRead0 != null) {
            for (Entry<Variable, InstanceType> e: lastWriter.entrySet()) {
                Variable var = e.getKey();
                assert !(var instanceof StackEntry);
                for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsWriteAfterRead0)
                    vis.discardPendingDataDependence(e.getValue(), var, DataDependenceType.WRITE_AFTER_READ);
            }
        }
        lastWriter.clear();

        if (pendingDataDependenceVisitorsReadAfterWrite0 != null) {
            for (Entry<Variable, List<InstanceType>> e: lastReaders.entrySet()) {
                Variable var = e.getKey();
                for (InstanceType inst: e.getValue())
                    for (DependencesVisitor<? super InstanceType> vis: pendingDataDependenceVisitorsReadAfterWrite0)
                        vis.discardPendingDataDependence(inst, var, DataDependenceType.READ_AFTER_WRITE);
            }
        }
        lastReaders.clear();
    }

    private Set<InstanceType> getInstanceIntersection(
            Set<Instruction> instructions, Set<InstanceType> instances) {

        if (instructions.isEmpty() || instances.isEmpty())
            return Collections.emptySet();

        Iterator<InstanceType> instanceIterator = instances.iterator();

        while (instanceIterator.hasNext()) {
            InstanceType inst = instanceIterator.next();
            if (instructions.contains(inst.getInstruction())) {
                Set<InstanceType> intersectInstances = new HashSet<InstanceType>();
                intersectInstances.add(inst);
                while (instanceIterator.hasNext()) {
                    inst = instanceIterator.next();
                    if (instructions.contains(inst.getInstruction()))
                        intersectInstances.add(inst);
                }
                return intersectInstances;
            }
        }

        return Collections.emptySet();
    }

    private static void computeControlDependences(ReadMethod method, IntegerMap<Set<Instruction>> controlDependences) {
    	// 计算一个方法的控制依赖，deps中的key是方法中的指令index，set是所有依赖与该条指令的指令！
    	// ControlFlowAnalyser.getInstance 返回的是一个ControlFlowAnalyser实例！
        Map<Instruction, Set<Instruction>> deps = ControlFlowAnalyser.getInstance().getInvControlDependences(method);
        for (Entry<Instruction, Set<Instruction>> entry: deps.entrySet()) {
            int index = entry.getKey().getIndex();
            assert !controlDependences.containsKey(index);
            controlDependences.put(index, entry.getValue()); // 将计算的结果添加到index指令对应的控制集合中！
        }
    }

    public void addProgressMonitor(ProgressMonitor progressMonitor) {
        this.progressMonitors.add(progressMonitor);
    }

    public void removeProgressMonitor(ProgressMonitor progressMonitor) {
        this.progressMonitors.remove(progressMonitor);
    }

}
