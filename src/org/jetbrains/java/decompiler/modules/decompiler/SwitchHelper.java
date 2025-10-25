// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.Pair;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public final class SwitchHelper {
  public static boolean simplifySwitches(Statement stat, StructMethod mt, RootStatement root) {
    boolean ret = false;
    if (stat instanceof SwitchStatement) {
      ret = simplify((SwitchStatement)stat, mt, root);
    }

    for (int i = 0; i < stat.getStats().size(); i++) {
      ret |= simplifySwitches(stat.getStats().get(i), mt, root);
    }

    return ret;
  }

  private static boolean simplify(SwitchStatement switchStatement, StructMethod mt, RootStatement root) {
    if (simplifySwitchOnEnumJ21(switchStatement, root)) {
      return true;
    }

    SwitchHeadExprent switchHeadExprent = (SwitchHeadExprent)switchStatement.getHeadexprent();
    Exprent value = switchHeadExprent.getValue();
    ArrayExprent array = getEnumArrayExprent(value, root);
    if (array != null) {
      List<List<Exprent>> caseValues = switchStatement.getCaseValues();
      Map<Exprent, Exprent> mapping = new HashMap<>(caseValues.size());
      if (array.getArray() instanceof FieldExprent arrayField) {
        ClassesProcessor.ClassNode classNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(arrayField.getClassname());
        if (classNode != null) {
          ClassWrapper classWrapper = classNode.getWrapper();
          if (classWrapper != null) {
            MethodWrapper wrapper = classWrapper.getMethodWrapper(CodeConstants.CLINIT_NAME, "()V");
            if (wrapper != null && wrapper.root != null) {
              // The enum array field's assignments if the field is built with a temporary local variable.
              // We need this to find the array field's values from the container class.
              List<AssignmentExprent> fieldAssignments = getAssignmentsOfWithinOneStatement(wrapper.root, arrayField);
              // If assigned more than once => not what we're looking for and discard the list
              if (fieldAssignments.size() > 1) {
                fieldAssignments.clear();
              }

              // Keep track of whether the assignment of the array field has already happened.
              // The same local variable might be used for multiple arrays (like with Kotlin, for example.)
              boolean[] fieldAssignmentEncountered = new boolean[] { false }; // single-element reference for lambdas

              wrapper.getOrBuildGraph().iterateExprents(exprent -> {
                if (exprent instanceof AssignmentExprent assignment) {
                  Exprent left = assignment.getLeft();
                  if (left instanceof ArrayExprent) {
                    Exprent assignmentArray = ((ArrayExprent) left).getArray();
                    // If the assignment target is a field, we have the assignment we want.
                    boolean targetsField = assignmentArray.equals(arrayField);

                    // If the target is a local variable, this gets more complicated.
                    // Kotlin (as mentioned above) creates its enum arrays by storing the array
                    // in a local first, so we need to check if the variable is later uniquely
                    // assigned to the enum array.
                    if (!targetsField && assignmentArray instanceof VarExprent && !fieldAssignmentEncountered[0]) {
                      for (AssignmentExprent fieldAssignment : fieldAssignments) {
                        if (fieldAssignment.getRight().equals(assignmentArray)) {
                          targetsField = true;
                          break;
                        }
                      }
                    }

                    if (targetsField && ((ArrayExprent) left).getIndex() instanceof InvocationExprent) {
                      mapping.put(assignment.getRight(), ((InvocationExprent) ((ArrayExprent) left).getIndex()).getInstance());
                    }
                  } else if (fieldAssignments.contains(exprent)) {
                    fieldAssignmentEncountered[0] = true;
                  }
                }
                return 0;
              });
            }
          }
        }
      } else { // Invocation
        InvocationExprent invocation = (InvocationExprent) array.getArray();
        ClassesProcessor.ClassNode classNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(invocation.getClassname());
        if (classNode != null) {
          ClassWrapper classWrapper = classNode.getWrapper();
          if (classWrapper != null) {
            MethodWrapper wrapper = classWrapper.getMethodWrapper(invocation.getName(), "()[I");
            if (wrapper != null && wrapper.root != null) {
              wrapper.getOrBuildGraph().iterateExprents(exprent -> {
                if (exprent instanceof AssignmentExprent) {
                  AssignmentExprent assignment = (AssignmentExprent) exprent;
                  Exprent left = assignment.getLeft();
                  if (left instanceof ArrayExprent) {
                    mapping.put(assignment.getRight(), ((InvocationExprent) ((ArrayExprent) left).getIndex()).getInstance());
                  }
                }
                return 0;
              });
            }
          } else {
            // Need to wait til last minute processing
            return false;
          }
        }
      }

      List<List<Exprent>> realCaseValues = new ArrayList<>(caseValues.size());
      for (List<Exprent> caseValue : caseValues) {
        List<Exprent> values = new ArrayList<>(caseValue.size());
        realCaseValues.add(values);
        cases:
        for (Exprent exprent : caseValue) {
          if (exprent == null) {
            values.add(null);
          }
          else {
            Exprent realConst = mapping.get(exprent);
            if (realConst == null) {
              if (exprent instanceof ConstExprent constLabel) {
                if (constLabel.getConstType().typeFamily == TypeFamily.INTEGER) {
                  int intLabel = constLabel.getIntValue();
                  // check for -1, used by nullable switches for the null branch
                  if (intLabel == -1) {
                    values.add(new ConstExprent(VarType.VARTYPE_NULL, null, null));
                    continue;
                  }
                  // other values can show up in a `tableswitch`, such as in [-1, fall-through synthetic 0, 1, 2, ...]
                  // they must have a valid value later though
                  // TODO: more tests
                  for (Exprent key : mapping.keySet()) {
                    if (key instanceof ConstExprent
                        && ((ConstExprent) key).getConstType().typeFamily == TypeFamily.INTEGER
                        && ((ConstExprent) key).getIntValue() > intLabel) {
                      values.add(key.copy());
                      continue cases;
                    }
                  }
                }
              }
              root.addComment("$VF: Unable to simplify switch on enum", true);
              DecompilerContext.getLogger()
                .writeMessage("Unable to simplify switch on enum: " + exprent + " not found, available: " + mapping + " in method " + mt.getClassQualifiedName() + " " + mt.getName(),
                              IFernflowerLogger.Severity.ERROR);
              return false;
            }
            values.add(realConst.copy());
          }
        }
      }
      caseValues.clear();
      caseValues.addAll(realCaseValues);
      Exprent newExpr = ((InvocationExprent)array.getIndex()).getInstance().copy();
      switchHeadExprent.replaceExprent(value, newExpr);
      newExpr.addBytecodeOffsets(value.bytecode);

      // If we replaced the only use of the local var, the variable should be removed altogether.
      if (value instanceof VarExprent valueVar) {
        List<Pair<Statement, Exprent>> references = new ArrayList<>();
        findExprents(root, Exprent.class, valueVar::isVarReferenced, false, (stat, expr) -> references.add(Pair.of(stat, expr)));

        // If we only have one reference...
        if (references.size() == 1) {
          // ...and if it's just an assignment, remove it.
          Pair<Statement, Exprent> ref = references.get(0);
          if (ref.b instanceof AssignmentExprent && ((AssignmentExprent) ref.b).getLeft().equals(value)) {
            ref.a.getExprents().remove(ref.b);
          }
        }
      }

      return true;
    } else {
      StringSwitchResult result = isSwitchOnString(switchStatement);
      if (result != null) {
        // Asserts not really needed, just in case is better than nothing maybe?
        assert result.target != null;

        Map<Integer, Exprent> caseMap = new HashMap<>();

        IfStatement containingNullCheck = null;
        if (result.type == StringSwitchResult.Type.SPLIT_NULLABLE) {
          assert result.nullAssignExpr != null;
          containingNullCheck = (IfStatement) switchStatement.getParent();
        }

        for (int i = 0; i < switchStatement.getCaseStatements().size(); ++i) {
          Statement curr = switchStatement.getCaseStatements().get(i);

          while (curr instanceof IfStatement ifStat)  {
            Exprent condition = ifStat.getHeadexprent().getCondition();

            if (condition instanceof FunctionExprent condFunction && condFunction.getFuncType() == FunctionType.NE) {
              condition = condFunction.getLstOperands().get(0);
            }

            if (condition instanceof InvocationExprent condInvocation && condInvocation.getLstParameters().size() == 1) {
              Exprent assign = ifStat.getIfstat().getExprents().get(0);
              int caseVal = ((ConstExprent)((AssignmentExprent)assign).getRight()).getIntValue();
              caseMap.put(caseVal, condInvocation.getLstParameters().get(0));
            }

            curr = ifStat.getElsestat();
          }
        }

        if (result.type == StringSwitchResult.Type.SPLIT_NULLABLE) {
          // the else branch of the containing `if` will have an assignment exprent to get the null case from
          Statement elseBranch = containingNullCheck.getElsestat();
          AssignmentExprent assign = (AssignmentExprent) elseBranch.getExprents().get(0);
          caseMap.put(((ConstExprent)assign.getRight()).getIntValue(), new ConstExprent(VarType.VARTYPE_NULL, null, null));
        }

        // Replace statement switch's case values with the original strings.
        List<List<Exprent>> realCaseValues = result.target.getCaseValues().stream()
          .map(l -> l.stream()
            .map(e -> e instanceof ConstExprent ? ((ConstExprent)e).getIntValue() : null)
            .map(caseMap::get)
            .collect(Collectors.toList()))
          .toList();
        result.target.getCaseValues().clear();
        result.target.getCaseValues().addAll(realCaseValues);

        // Replace the statement switch's condition to the first's value.
        Exprent followingVal = ((SwitchHeadExprent) result.target.getHeadexprent()).getValue();
        result.target.getHeadexprent().replaceExprent(followingVal, ((InvocationExprent) value).getInstance());

        // Remove lingering variable that are now unused. This is typically the statement switch's condition.
        // (the integer case value that is set in the first switch)
        var first = switchStatement.getFirst();
        List<Exprent> firstExprs = first.getExprents();
        if (!firstExprs.isEmpty()) {
          firstExprs.remove(firstExprs.size() - 1);
        }

        // Remove all connecting edges from the lingering variable block.
        first.getAllPredecessorEdges().forEach(first::removePredecessor);
        first.getAllSuccessorEdges().forEach(first::removeSuccessor);
        {
          // The statement switch being in the default block has a parent sequence which we want to keep.
          Statement replacement = result.type == StringSwitchResult.Type.SPLIT_INLINED
            ? result.target.getParent() : first;
          replacement.getAllPredecessorEdges().forEach(replacement::removePredecessor);
          switchStatement.replaceWith(replacement);
        }

        if (result.type == StringSwitchResult.Type.SPLIT_NULLABLE) {
          // remove the containing `if`
          Statement replaced = containingNullCheck.replaceWithEmpty();

          // Replace unneeded edges left over from the replaced block
          new HashSet<>(replaced.getLabelEdges())
            .forEach(e -> {
              result.target.removePredecessor(e);
              e.removeClosure();
            });
        }

        // Remove phantom references from old switch statement.
        // Ignore the first statement as that has been extracted out of the switch.
        result.target.getAllPredecessorEdges()
          .stream()
          .filter(e -> switchStatement.containsStatement(e.getSource()) && e.getSource() != first)
          .forEach(e -> e.getSource().removeSuccessor(e));

        return true;
      }
    }

    return false;
  }

  private static boolean simplifySwitchOnEnumJ21(SwitchStatement switchSt, RootStatement root) {
    SwitchHeadExprent head = (SwitchHeadExprent) switchSt.getHeadexprent();
    Exprent inner = head.getValue();

    Map<ConstExprent, String> mapping = new HashMap<>();
    List<List<Exprent>> values = switchSt.getCaseValues();
    for (List<Exprent> list : values) {
      for (Exprent v : list) {
        if (v == null) {
          continue; // Default case - fine
        }

        if (!(v instanceof ConstExprent)) {
          return false; // no const? can't do anything
        }

        if (v.getExprType().typeFamily != TypeFamily.INTEGER) {
          return false; // no integer, can't process
        }

        mapping.put((ConstExprent) v, null);
      }
    }

    // Best guess based on the ordinal
    if (inner instanceof InvocationExprent && ((InvocationExprent) inner).getName().equals("ordinal")) {
      InvocationExprent invInner = (InvocationExprent) inner;

      StructClass classStruct = DecompilerContext.getStructContext().getClass(invInner.getClassname());
      if (classStruct == null) {
        root.addComment("$VF: Unable to simplify switch-on-enum, as the enum class was not able to be found.", true);
        return false;
      }

      // Check for enum
      if ((classStruct.getAccessFlags() & CodeConstants.ACC_ENUM) == CodeConstants.ACC_ENUM) {
        List<String> enumNames = new ArrayList<>();

        // Capture fields
        for (StructField fd : classStruct.getFields()) {
          if ((fd.getAccessFlags() & CodeConstants.ACC_ENUM) == CodeConstants.ACC_ENUM) {
            enumNames.add(fd.getName());
          }
        }

        for (ConstExprent e : new HashSet<>(mapping.keySet())) {
          for (List<Exprent> lst : values) {
            for (int i = 0; i < lst.size(); i++) {
              Exprent ex = lst.get(i);

              if (e == ex) {
                // now do the replacement
                int idx = e.getIntValue();
                String name = enumNames.get(idx);
                lst.set(i, new FieldExprent(name, invInner.getClassname(), true, null, FieldDescriptor.parseDescriptor("L" + invInner.getClassname() + ";"), null));
              }
            }
          }
        }

        // Success! now let's clean it up. Remove "default -> throw new MatchException", if it exists
        // Only do this for switch expression (phantom) switches. Otherwise we might accidentally obliterate
        // definite assignment for a variable.
        if (switchSt.isPhantom()) {
          for (int i = 0; i < values.size(); i++) {
            List<Exprent> list = values.get(i);

            if (list.size() == 1 && list.get(0) == null) { // default by itself
              Statement st = switchSt.getCaseStatements().get(i);
              if (IfPatternMatchProcessor.isStatementMatchThrow(st)) {
                // Replace it with an empty block
                st.replaceWithEmpty();
              }
            }
          }
        }

        // Now replace the 'var.ordinal()' with 'var'
        head.replaceExprent(inner, ((InvocationExprent)inner).getInstance());

        return true;
      }
    }

    return false;
  }

  public static final int STATIC_FINAL_SYNTHETIC = CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL | CodeConstants.ACC_SYNTHETIC;
  /**
   * When Java introduced Enums they added the ability to use them in Switch statements.
   * This was done in a purely syntax sugar way using the old switch on int methods.
   * The compiler creates a synthetic class with a static int array field.
   * To support enums changing post compile, It initializes this field with a length of the current enum length.
   * And then for every referenced enum value it adds a mapping in the form of:
   *   try {
   *     field[Enum.VALUE.ordinal()] = 1;
   *   } catch (FieldNotFoundException e) {}
   *
   * If a class has multiple switches on multiple enums, the compiler adds the init and try list to the BEGINNING of the static initalizer.
   * But they add the field to the END of the fields list.
   *
   * Note: SOME compilers name the field starting with $SwitchMap, so if we do not have full context this can be a guess.
   * But Obfuscated/renamed code could cause issues
   */
  private static boolean isEnumArray(Exprent exprent) {
    if (exprent instanceof ArrayExprent) {
      ArrayExprent arr = (ArrayExprent) exprent;
      Exprent tmp = arr.getArray();
      if (tmp instanceof FieldExprent) {
        FieldExprent field = (FieldExprent)tmp;
        Exprent index = arr.getIndex();
        ClassesProcessor.ClassNode classNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(field.getClassname());

        if (classNode == null || !"[I".equals(field.getDescriptor().descriptorString)) {
          // TODO: tighten up this check to avoid false positives
          return field.getName().startsWith("$SwitchMap") || //This is non-standard but we don't have any more information so..
            (index instanceof InvocationExprent && ((InvocationExprent) index).getName().equals("ordinal")) && field.isStatic();
        }

        StructField stField;
        if (classNode.getWrapper() == null) { // I have no idea why this happens, according to debug tests it doesn't even return null
          stField = classNode.classStruct.getField(field.getName(), field.getDescriptor().descriptorString);
        } else {
          stField = classNode.getWrapper().getClassStruct().getField(field.getName(), field.getDescriptor().descriptorString);
        }

        if ((stField.getAccessFlags() & STATIC_FINAL_SYNTHETIC) != STATIC_FINAL_SYNTHETIC) {
          return false;
        }

        boolean isSyntheticClass;
        if (classNode.getWrapper() == null) {
          isSyntheticClass = (classNode.classStruct.getAccessFlags() & CodeConstants.ACC_SYNTHETIC) == CodeConstants.ACC_SYNTHETIC;
        } else {
          isSyntheticClass = (classNode.getWrapper().getClassStruct().getAccessFlags() & CodeConstants.ACC_SYNTHETIC) == CodeConstants.ACC_SYNTHETIC;
        }

        if (isSyntheticClass) {
          return true; //TODO: Find a way to check the structure of the initalizer?
          //Exprent init = classNode.getWrapper().getStaticFieldInitializers().getWithKey(InterpreterUtil.makeUniqueKey(field.getName(), field.getDescriptor().descriptorString));
          //Above is null because we haven't preocess the class yet?
        }
      } else if (tmp instanceof InvocationExprent) {
        InvocationExprent inv = (InvocationExprent) tmp;
        if (inv.getName().startsWith("$SWITCH_TABLE$")) { // More nonstandard behavior. Seems like eclipse compiler stuff: https://bugs.eclipse.org/bugs/show_bug.cgi?id=544521 TODO: needs tests!
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Gets the enum array exprent (or null if not found) corresponding to
   * the switch head. If the switch head itself is an enum array, returns the head.
   * If it's a variable only assigned to an enum array, returns that array.
   */
  private static ArrayExprent getEnumArrayExprent(Exprent switchHead, RootStatement root) {
    Exprent candidate = switchHead;

    if (switchHead instanceof FunctionExprent) {
      // Check for switches on a ternary expression like `a != null ? ...SwitchMap[a.ordinal()] : -1` (nullable switch)
      FunctionExprent func = (FunctionExprent) switchHead;
      if (func.getFuncType() == FunctionExprent.FunctionType.TERNARY && func.getLstOperands().size() == 3) {
        List<Exprent> ops = func.getLstOperands();
        if (ops.get(0) instanceof FunctionExprent) {
          FunctionExprent nn = (FunctionExprent) ops.get(0);
          if (nn.getFuncType() == FunctionExprent.FunctionType.NE
                && nn.getLstOperands().get(0) instanceof VarExprent
                && nn.getLstOperands().get(1).getExprType().equals(VarType.VARTYPE_NULL)) {
            // TODO: consider if verifying the variable used is necessary
            // probably not, since the array is checked to be generated (?) so user written code shouldn't encounter bad resugaring
            if (ops.get(2) instanceof ConstExprent) {
              ConstExprent minusOne = (ConstExprent) ops.get(2);
              if (minusOne.getConstType().equals(VarType.VARTYPE_INT) && minusOne.getIntValue() == -1) {
                candidate = ops.get(1);
              }
            }
          }
        }
      }
    }

    if (switchHead instanceof VarExprent) {
      // Check for switches with intermediary assignment of enum array index
      // This happens with Kotlin when expressions on enums.
      VarExprent var = (VarExprent) switchHead;

      if (!"I".equals(var.getVarType().toString())) {
        // Enum array index must be int
        return null;
      }

      List<AssignmentExprent> assignments = getAssignmentsOfWithinOneStatement(root, var);

      if (!assignments.isEmpty()) {
        if (assignments.size() == 1) {
          AssignmentExprent assignment = assignments.get(0);
          candidate = assignment.getRight();
        } else {
          // more than 1 assignment to variable => can't be what we're looking for
          return null;
        }
      }
    }

    return isEnumArray(candidate) ? (ArrayExprent) candidate : null;
  }

  /**
   * Recursively searches for assignments of the target that happen within one statement.
   * This is done as a list because the intended outcomes of the "1 found" (unique) and "2+ found" (non-unique) cases
   * are different. (But we don't need to have all the assignments within the root stat
   * because the non-unique case is a failure.)
   */
  private static List<AssignmentExprent> getAssignmentsOfWithinOneStatement(Statement start, Exprent target) {
    List<AssignmentExprent> exprents = new ArrayList<>();
    findExprents(start, AssignmentExprent.class, assignment -> assignment.getLeft().equals(target), true, (stat, expr) -> exprents.add(expr));
    return exprents;
  }

  /**
   * Recursively searches one statement for matching exprents.
   *
   * @param start       the statement to search
   * @param exprClass   the wanted exprent type
   * @param predicate   a predicate for filtering the exprents
   * @param onlyOneStat if true, will return eagerly after the first matching statement
   * @param consumer    the consumer that receives the exprents and their parent statements
   */
  // TODO: move somewhere better
  @SuppressWarnings("unchecked")
  public static <T extends Exprent> void findExprents(Statement start, Class<? extends T> exprClass, Predicate<T> predicate, boolean onlyOneStat, BiConsumer<Statement, T> consumer) {
    Queue<Statement> statQueue = new ArrayDeque<>();
    statQueue.offer(start);

    while (!statQueue.isEmpty()) {
      Statement stat = statQueue.remove();
      statQueue.addAll(stat.getStats());

      if (stat.getExprents() != null) {
        boolean foundAny = false;

        for (Exprent expr : stat.getExprents()) {
          if (exprClass.isInstance(expr) && predicate.test((T) expr)) {
            consumer.accept(stat, (T) expr);
            foundAny = true;
          }
        }

        if (onlyOneStat && foundAny) {
          break;
        }
      }
    }
  }

  /**
   * Switch on string gets compiled into two sequential switch statements.
   *   The first is a switch on the hashcode of the string with the case statement
   *   being the actual if equal to string literal check. Hashcode collisions result in
   *   an else if chain. The body of the if block sets the switch variable for the
   *   following switch.
   * <p>
   *   The statement switch block has the case statements of the original switch
   *   and may also be inlined directly into the first switch's default block.
   * <p>
   *   It is not guaranteed to exist, for example if the cases return out of the switch statement.
   *   In this scenario, instead of an intermediate variable the result is returned directly.
   *
   * <pre>
   * {@code
   *   byte var3 = -1;
   *   switch (var0.hashcode()) {
   *     case -390932093:
   *        if (var0.equals("foo")) {
   *          var3 = 0;
   *        }
   *   }
   *
   *   switch(var3) {
   *     case 0: // code for case "foo"
   *   }
   * }
   * </pre>
   *
   * @param first the first switch
   * @return the result if the switch is a string-switch; null otherwise
   */
  @Nullable
  private static StringSwitchResult isSwitchOnString(SwitchStatement first) {
    StringSwitchResult result = findSecondStringSwitch(first);

    if (result == null) {
      return null;
    }

    Exprent firstValue = ((SwitchHeadExprent) first.getHeadexprent()).getValue();
    if (!(firstValue instanceof InvocationExprent invExpr)
        || !invExpr.getName().equals("hashCode")
        || !invExpr.getClassname().equals("java/lang/String")
        || !(first.getCaseStatements().get(0) instanceof IfStatement)) {
      return null;
    }

    VarExprent varExpr = null;
    if (result.type == StringSwitchResult.Type.SPLIT) {
      // Should NEVER be null here because of split type, assert just in case.
      assert result.target != null;

      Exprent secondValue = ((SwitchHeadExprent) result.target.getHeadexprent()).getValue();
      if (!(secondValue instanceof VarExprent)) {
        return null;
      }
      varExpr = (VarExprent) secondValue;

      if (result.nullAssignExpr != null && !result.nullAssignExpr.getLeft().equals(varExpr)) {
        return null; // wrong assignment across `if`
      }
    }

    // Validate all of the case statements in the switch to make sure it matches the type found.
    for (int i = 0; i < first.getCaseStatements().size(); ++i) {
      Statement currStat = first.getCaseStatements().get(i);
      List<StatEdge> currEdge = first.getCaseEdges().get(i);

      // Skip default case because we determine a string-switch is valid based on all of the cases with values.
      if (currEdge.contains(first.getDefaultEdge())) {
        continue;
      }

      // Validate case if/else blocks.
      while (currStat != null) {
        if (!(currStat instanceof IfStatement ifStat)) {
          return null;
        }

        Exprent cond = ifStat.getHeadexprent().getCondition();
        if (cond instanceof FunctionExprent condFunc && condFunc.getFuncType() == FunctionType.NE) {
          cond = condFunc.getLstOperands().get(0);
        }

        // The if statement not containing an equals on the switch head exprent with the case string
        // means that this is not a string-switch.
        if (!(cond instanceof InvocationExprent condInvoc)
            || !condInvoc.getName().equals("equals")
            || !condInvoc.getInstance().equals(invExpr.getInstance())) {
          return null;
        }

        List<Exprent> block = ifStat.getIfstat().getExprents();
        if (block == null || block.size() != 1) {
          return null;
        }

        // Single/merged string-switch always has return statements
        if (result.type == StringSwitchResult.Type.MERGED && !isConstReturn(block.get(0))) {
          return null;
        }
        // Split string-switch always has variable assignment statements
        if (result.type != StringSwitchResult.Type.MERGED && !isConstAssignWithVar(block.get(0), varExpr)) {
          return null;
        }

        // All of our desired checks have passed, we know for sure that it's a valid string-switch. Yippee!
        // Validate the else blocks if they exist as well because multiple hash collision use if-else chains.
        currStat = ifStat.getElsestat();
      }
    }

    return result;
  }

  /**
   * Tries to find a related second switch statement from a given first switch.
   * In the case that the secondary string-switch is actually merged with the first switch, this will return null.
   * It will look for specifically a switch statement that is either on the succeeding edge of the first switch,
   * or a switch statement that is inlined into the default case of the first switch.
   *
   * @param first original switch to search from
   * @return a result object containing the type of the string-switch statement, the target (second) string-switch
   * if found, and the null assignment exprent for a nullable string-switch, otherwise `null` if nothing was found
   */
  @Nullable
  private static StringSwitchResult findSecondStringSwitch(SwitchStatement first) {
    {
      // Adjacent switch
      {
        final List<StatEdge> edges = first.getSuccessorEdges(StatEdge.TYPE_REGULAR);
        if (edges.size() == 1 && edges.get(0).getDestination() instanceof SwitchStatement target) {
          return new StringSwitchResult(StringSwitchResult.Type.SPLIT, target, null);
        }
      }
    }

    // Inlined-default switch
    if (first.getDefaultEdge() != null
      && first.getDefaultEdge().getDestination().getFirst() instanceof SwitchStatement target) {
      return new StringSwitchResult(StringSwitchResult.Type.SPLIT_INLINED, target, null);
    }

    // Nullable string-switch
    if (first.getParent() instanceof IfStatement parent && !first.hasSuccessor(StatEdge.TYPE_REGULAR)) {
      Exprent ifCond = parent.getHeadexprent().getCondition();
      // and it's a null check with `else` branch,
      if (parent.iftype == IfStatement.IFTYPE_IFELSE && ifCond instanceof FunctionExprent func) {
        if (func.getFuncType() == FunctionType.NE && func.getLstOperands().size() == 2) {
          Exprent right = func.getLstOperands().get(1);
          if (right instanceof ConstExprent && right.getExprType() == VarType.VARTYPE_NULL) {
            // and the `else` only assigns a variable,
            Statement elseStat = parent.getElsestat();
            if (elseStat instanceof BasicBlockStatement
              && elseStat.getExprents().size() == 1
              && elseStat.getExprents().get(0) instanceof AssignmentExprent nullAssignExpr) {
              // then we're probably a nullable string-switch
              final List<StatEdge> edges = parent.getSuccessorEdges(StatEdge.TYPE_REGULAR);
              if (edges.size() == 1 && edges.get(0).getDestination() instanceof SwitchStatement target) {
                return new StringSwitchResult(StringSwitchResult.Type.SPLIT_NULLABLE, target, nullAssignExpr);
              }
            }
          }
        }
      }
    }

    return null;
  }

  /**
   * Checks that the given exprent is a const assignment and that the assignment variable matches the var exprent.
   * @param expr exprent to check
   * @param varExpr var exprent to check
   * @return true if matched otherwise false
   */
  private static boolean isConstAssignWithVar(Exprent expr, VarExprent varExpr) {
    return expr instanceof AssignmentExprent assignExpr
      && assignExpr.getRight() instanceof ConstExprent
      && assignExpr.getLeft().equals(varExpr);
  }

  /**
   * Checks that the given exprent is a return with a constant value.
   * @param expr exprent to check
   * @return true if matched otherwise false
   */
  private static boolean isConstReturn(Exprent expr) {
    return expr instanceof ExitExprent exitExprent
      && exitExprent.getExitType() == ExitExprent.Type.RETURN
      && exitExprent.getValue() instanceof ConstExprent;
  }

  private record StringSwitchResult(Type type,
                                    @Nullable SwitchStatement target,
                                    @Nullable AssignmentExprent nullAssignExpr) {
    private enum Type {
      SPLIT,
      SPLIT_INLINED,
      SPLIT_NULLABLE,
      MERGED;
    };
  }
}
