/** License information:
 *    Component: javaslicer-core
 *    Package:   de.unisb.cs.st.javaslicer.slicing
 *    Class:     SliceInstructionsCollector
 *    Filename:  javaslicer-core/src/main/java/de/unisb/cs/st/javaslicer/slicing/SliceInstructionsCollector.java
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

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

//import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstance;
import de.unisb.cs.st.javaslicer.variables.Variable;


public class SliceInstructionsCollector implements SliceVisitor {

    private final Set<InstructionInstance> dynamicSlice = new HashSet<InstructionInstance>();
    
    @Override
    // visit the slice criterion
	public void visitMatchedInstance(InstructionInstance instance) {
        this.dynamicSlice.add(instance);
    }
     
    @Override
    // 计算依赖图的传递比包，from 依赖于 to 且 from已经在图中； 当是控制依赖的时候 variable 是null， 否则variable表示from读
    //而to写的那些变量； distance 表示距离切片标准的距离
	public void visitSliceDependence(InstructionInstance from,
    		InstructionInstance to, Variable variable, int distance) {
        this.dynamicSlice.add(to);
    }

    public Set<InstructionInstance> getDynamicSlice() {
        return Collections.unmodifiableSet(this.dynamicSlice);
    }

}
