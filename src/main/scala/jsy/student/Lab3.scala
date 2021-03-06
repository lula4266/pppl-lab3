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
      case (S(x),S(y)) => bop match {
        case Lt => x < y
        case Le => x <= y
        case Gt => x > y
        case Ge => x>= y
        case _ => ??? //throw new UnsupportedOperationException
      }
      case (x, y) => bop match{
        case Lt => toNumber(x) < toNumber(y)
        case Le => toNumber(x) <= toNumber(y)
        case Gt => toNumber(x) > toNumber(y)
        case Ge => toNumber(x) >= toNumber(y)
        case _ => ??? //throw new UnsupportedOperationException
      }
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
      case Function(p,x,y) => {
        Function(p,x,y)
      }


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
            (v1,v2) match{
              case (Function(_,_,_),_) => throw DynamicTypeError(e)
              case (_,Function(_,_,_)) => throw DynamicTypeError(e)
              case (_,_) =>{
                if(v1 == v2){
                  B(true)
                }
                else{
                  B(false)
                }
              }
            }
          }

          case Ne => {
            val v1 = eval(env, e1)
            val v2 = eval(env, e2)
            (v1, v2) match {
              case (Function(_, _, _), _) => throw DynamicTypeError(e)
              case (_, Function(_, _, _)) => throw DynamicTypeError(e)
              case (_, _) => {
                if (v1 != v2) {
                  B(true)
                } else {
                  B(false)
                }
              }
            }
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
              //case (Function(_,_,_),_) => throw DynamicTypeError(e)
              //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
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
              //case (Function(_,_,_),_) => throw DynamicTypeError(e)
              //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
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
             // case (Function(_,_,_),_) => throw DynamicTypeError(e)
              //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
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
              //case (Function(_,_,_),_) => throw DynamicTypeError(e)
              //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
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
            val v1 = eval(env, e1)
            val v2 = eval(env, e2)
            v2
          }
          case _ => throw DynamicTypeError(e)
        }
      }
      case If(e1, e2, e3) => if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
      case ConstDecl(x, e1, e2) => {
        val v:Expr = eval(env, e1) // Evaluate down to guarantee we are at a value, otherwise extend fails a require()
        val newEnv = extend(env, x, v) // Add the value to the env map, a running list of variables
        eval(newEnv, e2) // Evaluate following expressions with the scoped variable
      }
      case Print(e1) => println(pretty(eval(env, e1))); Undefined


        // ****** Your cases here

      case Call(e1, e2) => {
        eval(env,e1) match {
          case Function(Some(p),x,y)=>{
            val newEnv = extend(env,p,eval(env,e1))
            val newEnv2 = extend(newEnv,x,eval(newEnv,e2))
            eval(newEnv2,y)
        }
          case Function(None, x, y) => {
            val newEnv = extend(env,x,eval(env,e2))
            eval(newEnv,y)
          }
          case _ => throw DynamicTypeError(e)
        }
      }
      case _ => ???
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = {
      val v = next(e,n)
      v match {
        case Some(e1) => loop(e1,n+1)
        case None => e
      }
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop,substitute(e1,v,x))
      case Binary(bop, e1, e2) => Binary(bop,substitute(e1,v,x),substitute(e2,v,x))
      case If(e1, e2, e3) => If(substitute(e1,v,x),substitute(e2,v,x), substitute(e3,v,x))
      case Call(e1, e2) => Call(substitute(e1,v,x),substitute(e2,v,x))
      case Var(y) => {
        if (x==y) v
        else Var(y)
      }
      case Function(None, y, e1) => if(x==y) Function(None,y,e1) else Function(None,y,substitute(e1,v,x))
      case Function(Some(y1), y2, e1) => if(y1 == x || y2 == x) Function(Some(y1),y2,e1) else Function(Some(y1),y2,substitute(e1,v,x))
      case ConstDecl(y, e1, e2) => if(x==y) ConstDecl(y,substitute(e1,v,x),e2)else ConstDecl(y,substitute(e1,v,x),substitute(e2,v,x))
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case N(_)|B(_)|S(_)|Undefined|Function(_,_,_) => e
      case Unary(Neg,v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))


      case Binary(Plus,v1,v2) if isValue(v1) && isValue(v2) => (v1,v2) match{
        case (S(x),_) => S(x.concat(toStr(v2)))
        case (_,S(y)) => S(y.concat(toStr(v1)))
        case (_,__) => N(toNumber(v1)+toNumber(v2))
      }
      case Binary(bop @(Times|Minus|Div|Lt|Le|Gt|Ge),v1,v2) if isValue(v1) && isValue(v2) => bop match {
        case Times => N(toNumber(v1) * toNumber(v2))
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Div => N(toNumber(v1) / toNumber(v2))
        case Lt => (v1, v2) match {
          case (S(x), S(y)) => B(x < y)
          //case (Function(_,_,_),_) => throw DynamicTypeError(e)
          //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
          case (_, _) => B(toNumber(v1) < toNumber(v2))
        }
        case Le => (v1, v2) match {
          case (S(x), S(y)) => B(x <= y)
          //case (Function(_,_,_),_) => throw DynamicTypeError(e)
          //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
          case (_, _) => B(toNumber(v1) <= toNumber(v2))
        }
        case Gt => (v1, v2) match {
          case (S(x), S(y)) => B(x > y)
          //case (Function(_,_,_),_) => throw DynamicTypeError(e)
          //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
          case (_, _) => B(toNumber(v1) > toNumber(v2))
        }
        case Ge => (v1, v2) match {
          case (S(x), S(y)) => B(x >= y)
          //case (Function(_,_,_),_) => throw DynamicTypeError(e)
          //case (_,Function(_,_,_)) => throw DynamicTypeError(e)
          case (_, _) => B(toNumber(v1) >= toNumber(v2))
        }
      }
      case Binary(Seq,v1,e2) if isValue(v1) => e2
      case Binary(And, v1,e2) if isValue(v1) => if(toBoolean(v1)) e2 else v1
      case Binary(Or,v1,v2) if isValue(v1) => if(toBoolean(v1)) v1 else v2
      case Binary(Eq,v1,v2) if(isValue(v1) && isValue(v2)) =>  (v1,v2) match{
        case(Function(_,_,_),_) => throw DynamicTypeError(e)
        case (_,Function(_,_,_)) => throw DynamicTypeError(e)
        case (_,_) => v1 match{
          case N(n) => B(n == toNumber(v2))
          case S(s) => B(s == toStr(v2))
          case B(b) => B(b == toBoolean(v2))
        }
      }
      case Binary(Ne, v1,v2) if(isValue(v1) && isValue(v2)) => (v1,v2) match {
        case (Function(_, _, _), _) => throw DynamicTypeError(e)
        case (_, Function(_, _, _)) => throw DynamicTypeError(e)
        case (_, _) => v1 match {
          case N(n) => B(n != toNumber(v2))
          case S(s) => B(s != toStr(v2))
          case B(b) => B(b != toBoolean(v2))
        }
      }
      case If(v1,e2,e3) if(isValue(v1))=> if(toBoolean(v1)) e2 else e3
      case Call(v1,v2) if(isValue(v1) && isValue(v2))=>
        v1 match{
          case Function(None,x,y)=> substitute(y,v2,x)
          case Function(Some(p),x,y)=> substitute(substitute(y,v1,p),v2,x)
          case _ => throw DynamicTypeError(e)
        }
      case ConstDecl(x,v1,e2) if(isValue(v1))=> substitute(e2,v1,x)

      
        // ****** Your cases here
      
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      case Unary(uop,e1) => Unary(uop,step(e1))
      case Binary(bop @(Eq | Ne),v1,e2) if(isValue(v1)) => v1 match{
        case Function(_,_,_)=> throw DynamicTypeError(e)
        case _ => Binary(bop,v1,step(e2))
      }
      case Binary(bop @(Minus|Plus|Times|Div|Lt|Le|Gt|Ge),v1,e2) if(isValue(v1))=> Binary(bop,v1,step(e2))
      case Binary(bop,e1,e2) if(!isValue(e1)) => Binary(bop,step(e1),e2)
      case Call(e1,e2) => {
        if(isValue(e1)) e1 match{
        case Function(_,_,_)=> Call(e1,step(e2))
        case _ => throw DynamicTypeError(e)
        }
        else Call(step(e1),e2)
      }
      case If(e1,e2,e3) if(!isValue(e1)) => If(step(e1),e2,e3)
      case ConstDecl(x,e1,e2) if(!isValue(e1)) => ConstDecl(x,step(e1),e2)


      
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
