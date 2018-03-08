package jsy.student

import jsy.lab3.Lab3Like
import jsy.lab3.Parser.parse
import jsy.lab3.ast._
import jsy.tester.JavascriptyTester
import org.scalatest._

class Lab3Spec(lab3: Lab3Like) extends FlatSpec {
  import lab3._

  "eval/function" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Var(x))
    val e2 = Function(Some(f), x, Var(x))
    assert(evaluate(e1) == e1)
    assert(evaluate(e2) == e2)
  }

  "eval/call" should "evaluate a function using big-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(3))
  }

  it should "handle recursive functions using big-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(6))
  }

  "step/call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(3))
  }

  it should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(6))
  }

  "step/binaryEq" should "correctly evaluates if equal" in {
    val x = N(2)
    val y = N(2)
    val z = step(Binary(Eq, x, y))
    assert(z === B(true))
  }

  it should "throw error if arguments are function" in {
    val s = "x"
    val x = N(2)
    val y = N(2)
    assertThrows[DynamicTypeError] {
      step(Binary(Eq, Function(None, s, Binary(Plus, x, y)), x))
    }
  }

  "step/binaryNe" should "correctly evaluates of not equal" in {
    val x = N(2)
    val y = N(2)
    val z = step(Binary(Ne, x, y))
    assert(z === B(false))
  }

  it should "throw error if arguments are function" in {
    val s = "x"
    val x = N(2)
    val y = N(2)
    assertThrows[DynamicTypeError] {
      step(Binary(Ne, Function(None, s, Binary(Plus, x, y)), x))
    }
  }

  "step/unaryNeg" should "return neg of number" in {
    val x = N(2)
    val z = step(Unary(Neg, x))
    assert(z === N(-2))
  }

  "step/unaryNot" should "return not of boolean" in {
    val x = B(true)
    val z = step(Unary(Not, x))
    assert(z === B(false))
  }

  "step/binarySeq" should "return e2 of e1 is true" in {
    val x = N(2)
    val y = B(true)
    val z = step(Binary(Seq, x, y))
    assert(z === y)
  }

  "step/binaryPlus" should "return addition of numbers" in {
    val x = N(2)
    val y = N(3)
    val z = step(Binary(Plus, x, y))
    assert(z === N(5))
  }

  it should "return an addition if one is string" in {
    val x = S("x")
    val y = N(3)
    val z = step(Binary(Plus, x, y))
    assert(z === S("x3"))
  }

  it should "return an addition if both are string" in {
    val x = S("x")
    val y = S("y")
    val z = step(Binary(Plus, x, y))
    assert(z === S("xy"))
  }

  "step/binaryMinus" should "return a subtraction of numbers" in {
    val x = N(2)
    val y = N(1)
    val z = step(Binary(Minus, x, y))
    assert(z === N(1))
  }

  "step/binaryTimes" should "return a multiplication of numbers" in {
    val x = N(2)
    val y = N(1)
    val z = step(Binary(Times, x, y))
    assert(z === N(2))
  }

  "step/binaryDiv" should "return a division of numbers" in {
    val x = N(2)
    val y = N(1)
    val z = step(Binary(Div, x, y))
    assert(z === N(2))
  }

  "step/binaryLt" should "correctly evaluates with 2 numbers" in {
    val x = N(2)
    val y = N(3)
    val z = step(Binary(Lt, x, y))
    assert(z === B(true))
  }

  it should "correctly evaluates if one is string" in {
    val x = S("x")
    val y = N(3)
    val z = step(Binary(Lt, x, y))
    assert(z === B(false))
  }

  it should "correctly evaluates if both are string" in {
    val x = S("x")
    val y = S("yz")
    val z = step(Binary(Lt, x, y))
    assert(z === B(true))
  }

  "step/binaryLe" should "correctly evaluates with 2 numbers" in {
    val x = N(2)
    val y = N(2)
    val z = step(Binary(Le, x, y))
    assert(z === B(true))
  }

  it should "correctly evaluates if one is string" in {
    val x = S("x")
    val y = N(3)
    val z = step(Binary(Le, x, y))
    assert(z === B(false))
  }

  it should "correctly evaluates if both are string" in {
    val x = S("x")
    val y = S("y")
    val z = step(Binary(Le, x, y))
    assert(z === B(true))
  }

  "step/binaryGt" should "correctly evaluates with 2 numbers" in {
    val x = N(3)
    val y = N(2)
    val z = step(Binary(Gt, x, y))
    assert(z === B(true))
  }

  it should "correctly evaluates if one is string" in {
    val x = S("x")
    val y = N(3)
    val z = step(Binary(Gt, x, y))
    assert(z === B(false))
  }

  it should "correctly evaluates if both are string" in {
    val x = S("xz")
    val y = S("y")
    val z = step(Binary(Gt, x, y))
    assert(z === B(false))
  }

  "step/binaryGe" should "correctly evaluates with 2 numbers" in {
    val x = N(2)
    val y = N(2)
    val z = step(Binary(Ge, x, y))
    assert(z === B(true))
  }

  it should "correctly evaluates if one is string" in {
    val x = S("x")
    val y = N(3)
    val z = step(Binary(Ge, x, y))
    assert(z === B(false))
  }

  it should "correctly evaluates if both are string" in {
    val x = S("x")
    val y = S("y")
    val z = step(Binary(Ge, x, y))
    assert(z === B(false))
  }

  "step/binaryAnd" should "return e2 if e1 is true" in {
    val x = B(true)
    val y = N(3)
    val z = step(Binary(And, x, y))
    assert(z === y)
  }

  it should "return e1 if e1 is false" in {
    val x = B(false)
    val y = N(3)
    val z = step(Binary(And, x, y))
    assert(z === x)
  }

  "step/binaryOr" should "return e1 if e1 is true" in {
    val x = B(true)
    val y = N(3)
    val z = step(Binary(Or, x, y))
    assert(z === x)
  }

  it should "return e2 if e1 is false" in {
    val x = B(false)
    val y = N(3)
    val z = step(Binary(Or, x, y))
    assert(z === y)
  }

  "step/if" should "return e2 if e1 is true" in {
    val x = B(true)
    val y = N(3)
    val c = N(2)
    val z = step(If(x, y, c))
    assert(z === y)
  }

  it should "return e3 if e1 is false" in {
    val x = B(false)
    val y = N(3)
    val c = N(2)
    val z = step(If(x, y, c))
    assert(z === c)
  }

  "substitute" should "perform syntatic substitution respecting shadowing" in {
    val xplus1 = parse("x + 1")
    val twoplus1 = parse("2 + 1")
    assert(substitute(xplus1, N(2), "x") === twoplus1)
    val constx3 = parse("const x = 3; x")
    val shadowx = Binary(Plus, constx3, Var("x"))
    assert(substitute(shadowx, N(2), "x") === Binary(Plus, constx3, N(2)))
  }

  {
    val one = parse("1")

    "iterate" should "stop if the callback body returns None" in {
      assertResult(one) {
        iterate(one) { (_, _) => None }
      }
    }

    it should "increment the loop counter on each iteration and use e if the callback body returns Some(e)" in {
      assertResult(parse("--1")) {
        iterate(one) { (e: Expr, n: Int) =>
          if (n == 2) None else Some(Unary(Neg, e))
        }
      }
    }
  }

  /* Tests based on rules */

  {
    val xval = N(2)
    val envx = extend(empty, "x", xval)
    val varx = Var("x")

    val e1 = parse("2 - 1 - 1")
    val e1p = parse("1 - 1")
    val e2 = parse("3 - 1 - 1")
    val e2p = parse("2 - 1")
    val v1 = N(0)
    val v2 = N(1)

    val vidfunction = parse("function (x) { return x }")

    "EvalVar" should "perform EvalVar" in {
      assertResult(xval) {
        eval(envx, varx)
      }
    }

    "EvalNeg" should "perform EvalNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        eval(envx, Unary(Neg, e1))
      }
    }

    "EvalTypeErrorEquality1" should "perform EvalTypeErrorEquality1" in {
      intercept[DynamicTypeError] {
        eval(envx, Binary(Eq, vidfunction, e2))
      }
    }

    "DoNeg" should "perform DoNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        step(Unary(Neg, v1))
      }
    }

    "SearchUnary" should "perform SearchUnary" in {
      assertResult(Unary(Neg, e1p)) {
        step(Unary(Neg, e1))
      }
    }
  }
}

// An adapter class to pass in your Lab3 object.
class Lab3SpecRunner extends Lab3Spec(Lab3)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab3.
// The test expects a corresponding .ans file with the expected result.
class Lab3JsyTests extends JavascriptyTester(None, "lab3", Lab3)

class Lab3Suite extends Suites(
  new Lab3SpecRunner,
  new Lab3JsyTests
)
