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
package org.sosy_lab.cpachecker.cpa.smg;

import static org.junit.Assert.*;
import static org.mockito.Mockito.mock;

import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.TestLogManager;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cfa.types.c.CFunctionType;
import org.sosy_lab.cpachecker.cfa.types.c.CNumericTypes;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.smg.objects.SMGObject;
import org.sosy_lab.cpachecker.cpa.smg.objects.SMGRegion;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

public class CLangSMGTest {
  static private final CFunctionType functionType = CFunctionType.functionTypeWithReturnType(CNumericTypes.UNSIGNED_LONG_INT);
  static private final CFunctionDeclaration functionDeclaration = new CFunctionDeclaration(FileLocation.DUMMY, functionType, "foo", ImmutableList.<CParameterDeclaration>of());
  private CLangStackFrame sf;

  static private final LogManager logger = TestLogManager.getInstance();
  static private final CIdExpression id_expression = new CIdExpression(FileLocation.DUMMY, null, "label", null);

  private static CLangSMG getNewCLangSMG64() {
    return new CLangSMG(MachineModel.LINUX64);
  }

  @SuppressWarnings("unchecked")
  @Before
  public void setUp() {
    sf = new CLangStackFrame(functionDeclaration, MachineModel.LINUX64);
    CLangSMG.setPerformChecks(true, logger);
  }

  @Test
  public void CLangSMGConstructorTest() {
    CLangSMG smg = getNewCLangSMG64();

    assertEquals(0, smg.getStackFrames().size());
    assertEquals(1, smg.getHeapObjects().size());
    assertEquals(0, smg.getGlobalObjects().size());

    SMGRegion obj1 = new SMGRegion(8, "obj1");
    SMGRegion obj2 = new SMGRegion(8, "obj2");

    Integer val1 = Integer.valueOf(1);
    Integer val2 = Integer.valueOf(2);

    SMGEdgePointsTo pt = new SMGEdgePointsTo(val1, obj1, 0);
    SMGEdgeHasValue hv = new SMGEdgeHasValue(CNumericTypes.UNSIGNED_LONG_INT, 0, obj2, val2.intValue());

    smg.addValue(val1);
    smg.addValue(val2);
    smg.addHeapObject(obj1);
    smg.addGlobalObject(obj2);
    smg.addPointsToEdge(pt);
    smg.addHasValueEdge(hv);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));

    // Copy constructor

    CLangSMG smg_copy = new CLangSMG(smg);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg_copy));

    assertEquals(0, smg_copy.getStackFrames().size());
    assertEquals(2, smg_copy.getHeapObjects().size());
    assertEquals(1, smg_copy.getGlobalObjects().size());

    assertEquals(obj1, smg_copy.getObjectPointedBy(val1));

    SMGEdgeHasValueFilter filter = SMGEdgeHasValueFilter.objectFilter(obj2);
    assertEquals(hv, Iterables.getOnlyElement(smg_copy.getHVEdges(filter)));
  }

  @Test
  public void CLangSMGaddHeapObjectTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(8, "label");

    smg.addHeapObject(obj1);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    Set<SMGObject> heap_objs = smg.getHeapObjects();

    assertTrue(heap_objs.contains(obj1));
    assertFalse(heap_objs.contains(obj2));
    assertTrue(heap_objs.size() == 2);

    smg.addHeapObject(obj2);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    heap_objs = smg.getHeapObjects();

    assertTrue(heap_objs.contains(obj1));
    assertTrue(heap_objs.contains(obj2));
    assertEquals(heap_objs.size(), 3);
  }

  @Test(expected=IllegalArgumentException.class)
  public void CLangSMGaddHeapObjectTwiceTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj = new SMGRegion(8, "label");

    smg.addHeapObject(obj);
    smg.addHeapObject(obj);
  }

  @Test
  public void CLangSMGaddHeapObjectTwiceWithoutChecksTest() {
    CLangSMG.setPerformChecks(false, logger);
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj = new SMGRegion(8, "label");

    smg.addHeapObject(obj);
    smg.addHeapObject(obj);
    assertTrue("Asserting the test finished without exception", true);
  }

  @Test
  public void CLangSMGaddGlobalObjectTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(8, "another_label");

    smg.addGlobalObject(obj1);
    Map<String, SMGRegion> global_objects =smg.getGlobalObjects();

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    assertEquals(global_objects.size(), 1);
    assertTrue(global_objects.values().contains(obj1));

    smg.addGlobalObject(obj2);
    global_objects =smg.getGlobalObjects();

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    assertEquals(global_objects.size(), 2);
    assertTrue(global_objects.values().contains(obj1));
    assertTrue(global_objects.values().contains(obj2));
  }

  @Test(expected=IllegalArgumentException.class)
  public void CLangSMGaddGlobalObjectTwiceTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj = new SMGRegion(8, "label");

    smg.addGlobalObject(obj);
    smg.addGlobalObject(obj);
  }

  @Test(expected=IllegalArgumentException.class)
  public void CLangSMGaddGlobalObjectWithSameLabelTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(16, "label");

    smg.addGlobalObject(obj1);
    smg.addGlobalObject(obj2);
  }

  @Test
  public void CLangSMGaddStackObjectTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion diffobj1 = new SMGRegion(8, "difflabel");

    smg.addStackFrame(sf.getFunctionDeclaration());

    smg.addStackObject(obj1);
    CLangStackFrame current_frame = smg.getStackFrames().peek();

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    assertEquals(current_frame.getVariable("label"), obj1);
    assertEquals(current_frame.getVariables().size(), 1);

    smg.addStackObject(diffobj1);
    current_frame = smg.getStackFrames().peek();

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    assertEquals(current_frame.getVariable("label"), obj1);
    assertEquals(current_frame.getVariable("difflabel"), diffobj1);
    assertEquals(current_frame.getVariables().size(), 2);
  }

  @Test(expected=IllegalArgumentException.class)
  public void CLangSMGaddStackObjectTwiceTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");

    smg.addStackFrame(sf.getFunctionDeclaration());

    smg.addStackObject(obj1);
    smg.addStackObject(obj1);
  }

  @Test
  public void CLangSMGgetObjectForVisibleVariableTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(16, "label");
    SMGRegion obj3 = new SMGRegion(32, "label");

    assertNull(smg.getObjectForVisibleVariable(id_expression.getName()));
    smg.addGlobalObject(obj3);
    assertEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj3);

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj1);
    assertEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj1);

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj2);
    assertEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj2);
    assertNotEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj1);

    smg.addStackFrame(sf.getFunctionDeclaration());
    assertEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj3);
    assertNotEquals(smg.getObjectForVisibleVariable(id_expression.getName()), obj2);
  }

  @Test
  public void CLangSMGgetStackFramesTest() {
    CLangSMG smg = getNewCLangSMG64();
    assertEquals(smg.getStackFrames().size(), 0);

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(new SMGRegion(8, "frame1_1"));
    smg.addStackObject(new SMGRegion(8, "frame1_2"));
    smg.addStackObject(new SMGRegion(8, "frame1_3"));
    assertEquals(smg.getStackFrames().size(), 1);
    assertEquals(smg.getStackFrames().peek().getVariables().size(), 3);

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(new SMGRegion(8, "frame2_1"));
    smg.addStackObject(new SMGRegion(8, "frame2_2"));
    assertEquals(smg.getStackFrames().size(), 2);
    assertEquals(smg.getStackFrames().peek().getVariables().size(), 2);

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(new SMGRegion(8, "frame3_1"));
    assertEquals(smg.getStackFrames().size(), 3);
    assertEquals(smg.getStackFrames().peek().getVariables().size(), 1);

    smg.addStackFrame(sf.getFunctionDeclaration());
    assertEquals(smg.getStackFrames().size(), 4);
    assertEquals(smg.getStackFrames().peek().getVariables().size(), 0);
  }

  @Test
  public void CLangSMGgetHeapObjectsTest() {
    CLangSMG smg = getNewCLangSMG64();
    assertEquals(smg.getHeapObjects().size(), 1);

    smg.addHeapObject(new SMGRegion(8, "heap1"));
    assertEquals(smg.getHeapObjects().size(), 2);

    smg.addHeapObject(new SMGRegion(8, "heap2"));
    smg.addHeapObject(new SMGRegion(8, "heap3"));
    assertEquals(smg.getHeapObjects().size(), 4);
  }

  @Test
  public void CLangSMGgetGlobalObjectsTest() {
    CLangSMG smg = getNewCLangSMG64();
    assertEquals(smg.getGlobalObjects().size(), 0);

    smg.addGlobalObject(new SMGRegion(8, "heap1"));
    assertEquals(smg.getGlobalObjects().size(), 1);

    smg.addGlobalObject(new SMGRegion(8, "heap2"));
    smg.addGlobalObject(new SMGRegion(8, "heap3"));
    assertEquals(smg.getGlobalObjects().size(), 3);
  }

  @Test
  public void CLangSMGmemoryLeaksTest() {
    CLangSMG smg = getNewCLangSMG64();

    assertFalse(smg.hasMemoryLeaks());
    smg.setMemoryLeak();
    assertTrue(smg.hasMemoryLeaks());
  }

  @Test
  public void consistencyViolationDisjunctnessTest() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj = new SMGRegion(8, "label");

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addHeapObject(obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addGlobalObject(obj);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));

    smg = getNewCLangSMG64();
    smg.addStackFrame(sf.getFunctionDeclaration());

    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addHeapObject(obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addStackObject(obj);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));

    smg = getNewCLangSMG64();
    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addGlobalObject(obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addStackObject(obj);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }

  @Test
  public void consistencyViolationUnionTest() {
    CLangSMG smg = getNewCLangSMG64();
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    SMGRegion stack_obj = new SMGRegion(8, "stack_variable");
    SMGRegion heap_obj = new SMGRegion(8, "heap_object");
    SMGRegion global_obj = new SMGRegion(8, "global_variable");
    SMGRegion dummy_obj = new SMGRegion(8, "dummy_object");

    smg.addStackFrame(sf.getFunctionDeclaration());
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addStackObject(stack_obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addGlobalObject(global_obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addHeapObject(heap_obj);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addObject(dummy_obj);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }

  @Test
  public void consistencyViolationNullTest() {

    CLangSMG smg = getNewCLangSMG64();

    smg = getNewCLangSMG64();
    SMGObject null_object = smg.getHeapObjects().iterator().next();
    Integer some_value = Integer.valueOf(5);
    SMGEdgeHasValue edge = new SMGEdgeHasValue(mock(CType.class), 0, null_object, some_value);

    smg.addValue(some_value);
    smg.addHasValueEdge(edge);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }

  /**
   * Identical object in different frames is inconsistent
   */
  @Test
  public void consistencyViolationStackNamespaceTest1() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj1);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj1);
    assertFalse(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }

  /**
   * Two objects with same label (variable name) in different frames are not inconsistent
   */
  @Test
  public void consistencyViolationStackNamespaceTest2() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(16, "label");

    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj1);
    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj2);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }

  /**
   * Two objects with same label (variable name) on stack and global namespace are not inconsistent
   */
  @Test
  public void consistencyViolationStackNamespaceTest3() {
    CLangSMG smg = getNewCLangSMG64();
    SMGRegion obj1 = new SMGRegion(8, "label");
    SMGRegion obj2 = new SMGRegion(16, "label");

    smg.addGlobalObject(obj1);
    smg.addStackFrame(sf.getFunctionDeclaration());
    smg.addStackObject(obj2);
    assertTrue(CLangSMGConsistencyVerifier.verifyCLangSMG(logger, smg));
  }
}
