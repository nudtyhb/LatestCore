package de.unisb.cs.st.javaslicer.slicing;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

import org.junit.Test;

import de.unisb.cs.st.javaslicer.AbstractSlicingTest;
import de.unisb.cs.st.javaslicer.common.classRepresentation.Instruction;
import de.unisb.cs.st.javaslicer.common.classRepresentation.InstructionInstance;


public class Testyhb_test extends AbstractSlicingTest {

    @Test
    public void testAll() throws IllegalArgumentException, IOException, URISyntaxException, InterruptedException {
	final List<InstructionInstance> slice = getSlice("/traces/yhb2.trace", "main", "test_yhb7.main:8:{y}");
	 InstructionInstance[] sliceArray = slice.toArray(new InstructionInstance[slice.size()]); // convert the set to array
     Arrays.sort(sliceArray);  // in order to ensure the sequence of dynamic execution
     System.out.println("result is: ");
     for (InstructionInstance insn: sliceArray) {
         System.out.format((Locale)null, "%s.%s:%d %s%n",
                 insn.getInstruction().getMethod().getReadClass().getName(),
                 insn.getInstruction().getMethod().getName(),
                 insn.getInstruction().getLineNumber(),
                 insn.getInstruction().toString());
     }
     System.out.format((Locale)null, "%nSlice consists of %d bytecode instructions.%n", sliceArray.length);
}
}
