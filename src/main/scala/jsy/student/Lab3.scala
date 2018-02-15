package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(str) => {
        try{
          str.toDouble
        }
        catch{
          case e: NumberFormatException => Double.NaN
        }
      }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n == 0 || n.isNaN) false else true
      case B(b) => b
      case S(str) => if (str == "") false else true
      case Undefined => false
      case Function(_, _, _) => true
      case _ => ??? // delete this line when done
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n match {
        //case negative if n < 0 => "-" + toStr(N(-n)) // saves us a few cases
        // case zero if n==0 => "0"
        //case infinity if n.isInfinity => "Infinity"
        case isWhole if n.isWhole() => isWhole.toInt.toString
        case notWhole => notWhole.toString
        case _ => "NaN"
      }
      case B(b) => if (b) "true" else "false"
      case S(s) => s
      case Undefined => "undefined"
      case Function(_, _, _) => "function"
      case _ => ??? // delete this line when done
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case _ => ??? // delete this line when done
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case Var(x) => lookup(env, x) // Get value associated in env map with our string
      case N(n) => N(n)
      case B(b) => B(b)
      case S(str) => S(str)
      case Undefined => Undefined
      case Function(_, _, _) => e
      case Var(x) => ???

      /* Inductive Cases */
      case Unary(uop, e1) => {
        uop match {
          case Neg => {
            val v1 = eval(env,e1)
            val np = -toNumber(v1)
            N(np)
          }
          case Not => {
            val v1 = eval(env,e1)
            val bp = !toBoolean(v1)
            B(bp)
          }
        }
      }
      case Binary(bop, e1, e2) => {
        bop match {
          case Plus => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            (v1,v2) match {
              case (S(x), _) => {
                val str = toStr(v2)
                S(x.concat(str))
              }
              case (_, S(y)) =>{
                val str = toStr(v1)
                S(str.concat(y))
              }
              case (_,_) => N(toNumber(v1)+toNumber(v2))
            }
          }
          case Minus => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)-toNumber(v2)
            N(np)
          }
          case Times => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)*toNumber(v2)
            N(np)
          }
          case Div => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)/toNumber(v2)
            N(np)
          }
          case Eq => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            if(v1 == v2){
              B(true)
            }
            else{
              B(false)
            }

          }
          case Ne => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)

            if(v1 != v2) {
              B(true)
            }else { B(false)}

          }
          case Lt => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison < 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) < toNumber(v2))
            }
          }
          case Le => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison <= 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) <= toNumber(v2))
            }
          }
          case Gt => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison > 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) > toNumber(v2))
            }
          }
          case Ge => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison >= 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) >= toNumber(v2))
            }
          }

          case And => {
            val v1 = eval(env, e1)
            if (toBoolean(v1)) eval(env, e2) else v1
          }
          case Or => {
            val v1 = eval(env, e1)
            if (toBoolean(v1)) v1 else eval(env, e2)
          }
          case Seq => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            v2
          }
        }
      }
      case If(e1, e2, e3) => if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
      case ConstDecl(x, e1, e2) => {
        val v:Expr = eval(env, e1) // Evaluate down to guarantee we are at a value, otherwise extend fails a require()
        val newEnv = extend(env, x, v) // Add the value to the env map, a running list of variables
        eval(newEnv, e2) // Evaluate following expressions with the scoped variable
      }
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case _ => ???

        // ****** Your cases here

      case Call(e1, e2) => ???
      case _ => ??? // delete this line when done
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = ???
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => ???
      case Binary(bop, e1, e2) => ???
      case If(e1, e2, e3) => ???
      case Call(e1, e2) => ???
      case Var(y) => ???
      case Function(None, y, e1) => ???
      case Function(Some(y1), y2, e1) => ???
      case ConstDecl(y, e1, e2) => ???
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
        // ****** Your cases here
      
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      
        // ****** Your cases here

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
