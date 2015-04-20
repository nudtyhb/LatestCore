/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.instructionSimulation
 *    Class:     SimulationEnvironment
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/instructionSimulation/SimulationEnvironment.java
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
package de.unisb.cs.st.javaslicer.instructionSimulation;

import java.util.AbstractCollection;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import de.hammacher.util.iterators.EmptyIterator;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.ReadMethod;
import de.unisb.cs.st.javaslicer.variables.LocalVariable;
import de.unisb.cs.st.javaslicer.variables.StackEntry;
import de.unisb.cs.st.javaslicer.variables.Variable;

// 注意SimulationEnvironment is not for only one method, but for the whole execution !
public class SimulationEnvironment {
 
	// 包含子类信息：
	// 1. AllVariables(local and stackEntry!) 
	// 2. cachedLocalVariables(数组格式)
	// 3. cachedStackEntries
	public static class AllVariables extends AbstractCollection<Variable> {

		public static class Itr implements Iterator<Variable> {

			private final LocalVariable[] localVars;
			private final StackEntry[] stackEntries;
			private int posLocalVars;  // 返回数组中从当前开始第一个非空元素的位置！
			private int posStackEntries; 

			public Itr(LocalVariable[] localVars, StackEntry[] stackEntries) {
				this.localVars = localVars;
				this.stackEntries = stackEntries;
				int firstLocalVar = 0;
				while (firstLocalVar < localVars.length && localVars[firstLocalVar] == null)
					++firstLocalVar;
				int firstStackEntry = 0;
				if (firstLocalVar == localVars.length) {
					while (firstStackEntry < stackEntries.length && stackEntries[firstStackEntry] == null)
						++firstStackEntry;
				}
				this.posLocalVars = firstLocalVar;
				this.posStackEntries = firstStackEntry;
			}

			@Override
			// hasnext判定依据的是posStackEntry, 而posStackEntry的改变依赖与next函数
			public boolean hasNext() {
				return this.posStackEntries == this.stackEntries.length;
			}

			// pos返回的是数组中下一个非空的位置！
			@Override
			public Variable next() {
				// 只有当stackEntry都没有非空位置的时候才使得hasnext为假的！
				if (!hasNext()) 
					throw new NoSuchElementException();
			
				Variable ret;
				if (this.posLocalVars == this.localVars.length) { 
					ret = this.stackEntries[this.posStackEntries];
					// 获取了以后要将pos设为下一个非空的位置！
					do {
						++this.posStackEntries;
					} while (this.posStackEntries < this.stackEntries.length && this.stackEntries[this.posStackEntries] == null);
				} else {
					ret = this.localVars[this.posLocalVars];
					// 返回了以后，要将pos设为下一个非空的位置！
					do {
						++this.posLocalVars;  
					} while (this.posLocalVars < this.localVars.length && this.localVars[this.posLocalVars] == null);
					
					// localVar 不能满足取的时候，调整StackEntry的pos用来取！
					if (this.posLocalVars == this.localVars.length)
						while (this.posStackEntries < this.stackEntries.length && this.stackEntries[this.posStackEntries] == null)
							++this.posStackEntries; 
				}
				return ret;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}

		}

		private int count; // LocalVars 和 stackEntries中非空元素个数的总和！
		private final LocalVariable[] localVars;
		private final StackEntry[] stackEntries;

		public AllVariables(LocalVariable[] localVariables,
				StackEntry[] stackEntries) {
			this.count = 0;
			for (LocalVariable var: localVariables)
				if (var != null)
					++this.count;
			for (StackEntry e: stackEntries)
				if (e != null)
					++this.count;
			this.localVars = localVariables;
			this.stackEntries = stackEntries;
		}

		@Override
		public int size() {
			return this.count;
		}

		@Override
		public Iterator<Variable> iterator() {
			return this.count == 0 ? EmptyIterator.<Variable>getInstance() : new Itr(this.localVars, this.stackEntries);
		}

	}
//-------------- end of all variables -------------------------------------------------------------------------------------
	
	public static class CachedLocalVariables extends AbstractList<LocalVariable> {

		private final LocalVariable[] entries;
		private final int offset;
		private final int amount;

		public CachedLocalVariables(LocalVariable[] entries, int offset,
				int amount) {
			this.entries = entries;
			this.offset = offset;
			this.amount = amount;
		}

		@Override
		public LocalVariable get(int index) {
			assert (index < this.amount);
			return this.entries[this.offset + index];
		}

		@Override
		public int size() {
			return this.amount;
		}
	}

	public static class CachedStackEntries extends AbstractList<StackEntry> {
		private final StackEntry[] entries;
		private final int offset;
		private final int amount;

		public CachedStackEntries(StackEntry[] entries, int offset,
				int amount) {
			this.entries = entries;
			this.offset = offset;
			this.amount = amount;
		}

		@Override
		public StackEntry get(int index) {
			assert (index < this.amount);
			return this.entries[this.offset + index];
		}

		@Override
		public int size() {
			return this.amount;
		}
	}

	// -------------------------member of simulationEnvironment!
	// frame本身对应于一个方法， 只有切片进入一个方法内才使得 NextFrame++, 才会更新frame[stackDepth].
	// 实际表示扫描到的方法的编号！
	public final long[] frames;  //frame含义:  frame下标为被调用方法对应的stackDepth，值为该方法被扫描到的排序Nr！
	public final int[] opStack;  // opStack 为 Operand Stack 即操作数栈！
	public final int[] minOpStack;  
	private final StackEntry[][] cachedStackEntries; // 第一维确定当前栈的深度，第二维是缓存的stackEntry
	private final LocalVariable[][] cachedLocalVariables; // 第一维是栈的深度，第二维是缓存的LocalVariable!

    /**
     * <code>true</code> if the next visited instruction in this frame must
     * have thrown an exception
     */
	public final boolean[] throwsException;
	public ReadMethod removedMethod; // 逆向访问到方法调用，刚扫描完的method!
	public Instruction[] lastInstruction; //每个栈的深度下最新扫描到的指令！
	public ReadMethod[] method; // 每个栈深度下最新处理的方法！

    /**
     * <code>true</code> if this frame was aborted abnormally (NOT by a RETURN
     * instruction), or catched an exception. In both cases, the control flow
     * was interrupted, so the stack entry indexes cannot be computed precisely
     * any more.
     */
	public boolean[] interruptedControlFlow;

	public SimulationEnvironment(long[] frames, int[] opStack,
			int[] minOpStack, //
			StackEntry[][] cachedStackEntries, //
			LocalVariable[][] cachedLocalVariables, //
			boolean[] throwsException,
			Instruction[] lastInstruction,
			ReadMethod[] method,
			boolean[] interruptedControlFlow) {
		this.frames = frames;
		this.opStack = opStack;
		this.minOpStack = minOpStack;
		this.cachedStackEntries = cachedStackEntries;
		this.cachedLocalVariables = cachedLocalVariables;
		this.throwsException = throwsException;
		this.lastInstruction = lastInstruction;
		this.method = method;
		this.interruptedControlFlow = interruptedControlFlow;
	}

	// 返回cachedlocalVariables中特定栈深度下的局部变量！-------------------------------------------------------------------------------------------------------
	public LocalVariable getLocalVariable(int stackDepth, int varIndex) {
		LocalVariable[] cached = this.cachedLocalVariables[stackDepth];
		if (cached==null || cached.length <= varIndex) {
			if(cached==null){
				this.cachedLocalVariables[stackDepth] = cached = new LocalVariable[varIndex*2+1] ;
			}
			else{
				this.cachedLocalVariables[stackDepth] = cached = Arrays.copyOf(cached,
						2*Math.max(Integer.highestOneBit(varIndex), cached.length));
			}
		}
		LocalVariable entry = cached[varIndex];
		// 如果为null,则新建一个特定frame,varIndex,method指定的localVariable
		if (entry == null)
			cached[varIndex] = entry = new LocalVariable(this.frames[stackDepth], varIndex, this.method[stackDepth]);
			//System.out.println("null of entry*************************************************\n");
		/*
		else
			{ if(this.method[stackDepth].getName().contains("main")){
			System.out.println("not null of entry**************************************************\n");
			  if(entry.getVarName().contains("a")){
				  System.out.println("index of  a is :");
				  System.out.print(varIndex);
				  System.out.println("\n");
			  }
			  if(entry.getVarName().contains("b")){
				  System.out.println("index of  b is :");
				  System.out.print(varIndex);
				  System.out.println("\n");
			  }
			  if(entry.getVarName().contains("c")){
				  System.out.println("index of  c is :");
				  System.out.print(varIndex);
				  System.out.println("\n");
			  }}
			}*/

		assert (entry.getFrame() == this.frames[stackDepth] && entry.getVarIndex() == varIndex);
		return entry;
	}

	
	// 返回cachlocalVariables中从index开始的大小为amount个变量集合！----------------------------------------------------------------------------------
	public Collection<LocalVariable> getLocalVariables(int stackDepth, int index, int amount) {
		if (amount <= 1)
			return amount == 0 ? Collections.<LocalVariable>emptySet() : Collections.singleton(getLocalVariable(stackDepth, index));

		LocalVariable[] cached = this.cachedLocalVariables[stackDepth];

		if (cached.length < index + amount) {
			this.cachedLocalVariables[stackDepth] = cached = Arrays.copyOf(cached,
				2*Math.max(Integer.highestOneBit(index+amount), cached.length));
		}

		for (int i = 0; i < amount; ++i) {
			if (cached[index + i] == null)
				cached[index + i] = new LocalVariable(this.frames[stackDepth], index + i, this.method[stackDepth]);
			assert (cached[index + i].getFrame() == this.frames[stackDepth] && cached[index + i].getVarIndex() == index+i);
		}

		return new CachedLocalVariables(cached, index, amount);
	}

	// 返回cachedStackEntry中stackDepth下，index 为 stackOffset的stackEntry--------------------------------------
	public StackEntry getOpStackEntry(int stackDepth, int stackOffset) {
		// stackOffset小于0， 更新minOpstack; 并且新建一个StackEntry(frame,stackOffset)
		if (stackOffset < 0) {
			if (stackOffset < this.minOpStack[stackDepth])
				this.minOpStack[stackDepth] = stackOffset;
			return new StackEntry(this.frames[stackDepth], stackOffset);			
		}
		// 获取特定栈深度下，stackEntry数组
		StackEntry[] cached = this.cachedStackEntries[stackDepth];
		if (cached.length <= stackOffset) {
			this.cachedStackEntries[stackDepth] = cached = Arrays.copyOf(cached,
				2*Math.max(Integer.highestOneBit(stackOffset), cached.length));
		}

		StackEntry entry = cached[stackOffset];
		// entry为空时，重新定义一个StackEntry(frame,index)
		if (entry == null)
			cached[stackOffset] = entry = new StackEntry(this.frames[stackDepth], stackOffset);
		assert (entry.getFrame() == this.frames[stackDepth] && entry.getIndex() == stackOffset);
		return entry;
	}

	// 
	public List<StackEntry> getOpStackEntries(int stackDepth, int stackOffset, int amount) {
		if (amount <= 1)
			return amount == 0 ? Collections.<StackEntry>emptyList() : Collections.singletonList(getOpStackEntry(stackDepth, stackOffset));

		if (stackOffset < 0) {
			if (stackOffset < this.minOpStack[stackDepth])
				this.minOpStack[stackDepth] = stackOffset;
			// unoptimized:
			List<StackEntry> list = new ArrayList<StackEntry>();
			for (int i = 0; i < amount; ++i)
				list.add(getOpStackEntry(stackDepth, stackOffset + i));
			return list;
		}

		StackEntry[] cached = this.cachedStackEntries[stackDepth];

		if (cached.length < stackOffset + amount) {
			this.cachedStackEntries[stackDepth] = cached = Arrays.copyOf(cached,
				2*Math.max(Integer.highestOneBit(stackOffset+amount), cached.length));
		}

		for (int i = 0; i < amount; ++i) {
			if (cached[stackOffset + i] == null)
				cached[stackOffset + i] = new StackEntry(this.frames[stackDepth], stackOffset + i);
			assert (cached[stackOffset + i].getFrame() == this.frames[stackDepth] && cached[stackOffset + i].getIndex() == stackOffset+i);
		}

		return new CachedStackEntries(cached, stackOffset, amount);
	}

	public int getAndIncOpStack(int stackDepth) {
		return this.opStack[stackDepth]++;
	}

	public int incAndGetOpStack(int stackDepth) {
		return ++this.opStack[stackDepth];
	}

	public int getAndDecOpStack(int stackDepth) {
		return this.opStack[stackDepth]--;
	}

	public int decAndGetOpStack(int stackDepth) {
		return --this.opStack[stackDepth];
	}

	public int getAndAddOpStack(int stackDepth, int amount) {
		int old = this.opStack[stackDepth];
		this.opStack[stackDepth] += amount;
		return old;
	}

	public int addAndGetOpStack(int stackDepth, int amount) {
		return this.opStack[stackDepth] += amount;
	}

	public int getAndSubOpStack(int stackDepth, int amount) {
		int old = this.opStack[stackDepth];
		this.opStack[stackDepth] -= amount;
		return old;
	}

	public int subAndGetOpStack(int stackDepth, int amount) {
		return this.opStack[stackDepth] -= amount;
	}

	public int getOpStack(int stackDepth) {
		return this.opStack[stackDepth];
	}

	public Collection<Variable> getAllVariables(int stackDepth) {
		return new AllVariables(this.cachedLocalVariables[stackDepth], this.cachedStackEntries[stackDepth]);
	}

}
