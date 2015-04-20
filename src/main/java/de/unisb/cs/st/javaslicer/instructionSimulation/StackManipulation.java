/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.instructionSimulation
 *    Class:     StackManipulation
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/instructionSimulation/StackManipulation.java
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

import java.util.Collection;
import java.util.Collections;
import java.util.Map;

import de.unisb.cs.st.javaslicer.variables.StackEntry;
import de.unisb.cs.st.javaslicer.variables.Variable;

// DynamicInfo 的一种实现：
public class StackManipulation<InstanceType> implements DynamicInformation {

	private final SimulationEnvironment simEnv;
	private final int stackDepth; // 操作对应的栈深度
    private final int read; //表示从stack 中读取多少个var
    private final int write; // 表示从stack中写多少个var
    private final int stackOffset; // 表示当前stack操作的基偏移量
    private Collection<StackEntry> usedVars = null; // 使用的变量为stackEntry类型
    private final Map<Long, Collection<? extends Variable>> createdObjects; // 创建的对象

    public StackManipulation(SimulationEnvironment simEnv, int stackDepth, int read, int write,
            int stackOffset, Map<Long, Collection<? extends Variable>> createdObjects) {
        this.simEnv = simEnv;
        this.stackDepth = stackDepth;
        this.read = read; 
        this.write = write; 
        this.stackOffset = stackOffset;
        this.createdObjects = createdObjects;
    }

    @Override
	public Collection<StackEntry> getDefinedVariables() {
        if (this.write == 0)
            return Collections.emptySet();

        Collection<StackEntry> definedVars;
        if (this.write == 1) {
            definedVars = Collections.singleton(this.simEnv.getOpStackEntry(this.stackDepth, this.stackOffset));
        } else {
            definedVars = this.simEnv.getOpStackEntries(this.stackDepth, this.stackOffset, this.write);
        }
        if (this.read == this.write)
        	// 因为Simple 面向的是Load 和Store类型的操作！
            this.usedVars = definedVars;  //当read和write相同时，usedVars和definedVars相同
        return definedVars;
    }

    @Override
	public Collection<StackEntry> getUsedVariables() {
        if (this.usedVars != null)
            return this.usedVars;

        if (this.read == 0)
            this.usedVars = Collections.emptySet();
        else if (this.read == 1)
            this.usedVars = Collections.singleton(this.simEnv.getOpStackEntry(this.stackDepth, this.stackOffset));
        else
            this.usedVars = this.simEnv.getOpStackEntries(this.stackDepth, this.stackOffset, this.read);

        return this.usedVars;
    }

    @Override
	public Collection<StackEntry> getUsedVariables(Variable definedVariable) {
        return getUsedVariables();
    }

    @Override
	public boolean isCatchBlock() {
        return false;
    }

    @Override
	public Map<Long, Collection<? extends Variable>> getCreatedObjects() {
        return this.createdObjects;
    }

}
