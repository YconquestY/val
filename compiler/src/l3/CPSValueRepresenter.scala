package l3

import l3.{ HighCPSTreeModule as H }
import l3.{ LowCPSTreeModule  as L }
import l3.{ L3Primitive as L3 }
import l3.{ CPSValuePrimitive as CPSV }
import l3.{ CPSTestPrimitive  as CPST }
import CL3Literal._
import BlockTag._

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    h2lVal(tree)(emptySubst[Symbol])

  private def h2lVal(tree: H.Tree)(_substitutions: Subst[Symbol]): L.Tree = {
    
    def extractEnv(env: Symbol, body: H.Tree)
                  (substitutions: Subst[Symbol], fvs: Seq[Symbol]): L.Tree =
      fvs match {
        case Seq() =>
          h2lVal(body)(substitutions)
        case fv +: fvs =>
          tmpLetP(CPSV.BlockGet, Seq(env, substitutions.size), { // `substition` is initially "f -> env" with size 1.
            (v: L.Name) => extractEnv(env, body)(substitutions + (fv -> v), fvs)
          })
      }

    tree match {
      case H.LetC(cnts: Seq[H.Cnt], body: H.Body) =>
        L.LetC(cnts.map {
            case H.Cnt(name, args, e) =>
              L.Cnt(name, args, h2lVal(e)(_substitutions))
        }, h2lVal(body)(_substitutions))
      case H.AppC(cnt: H.Name, args: Seq[H.Atom]) =>
        L.AppC(cnt, args.map(rewrite(_)(_substitutions)))
      // function
      // not improved yet!
      case H.LetF(funs: Seq[H.Fun], body: H.Body) => {
        val (closedFuns, mappings) = funs.map {
          case H.Fun(f: Symbol, retC: H.Name, args: Seq[H.Name], e: H.Body) => {
            val w   = Symbol.fresh("w")
            val env = Symbol.fresh("env")
            val fvs = ((fv(e) - f) diff args.toSet).toSeq

            (L.Fun(w, retC, env +: args, extractEnv(env, e)(subst(f, env), fvs)),
             f -> (w, fvs))
          }
        }.unzip

        var WIP: L.Tree = h2lVal(body)(_substitutions)
        for ((f, (w, fvs)) <- mappings) {
          for ((fv, index) <- fvs.zipWithIndex) {
            WIP = L.LetP(Symbol.fresh("t"), CPSV.BlockSet, Seq(f, index + 1, fv), WIP)
          }
          WIP = L.LetP(Symbol.fresh("t"), CPSV.BlockSet, Seq(f, 0, w), WIP)
        }
        for ((f, (w, fvs)) <- mappings) {
          WIP = L.LetP(f, CPSV.BlockAlloc, Seq(BlockTag.Function, fvs.size + 1), WIP)
        }

        L.LetF(closedFuns, WIP)
      }
      case H.AppF(fun: H.Name, retC: H.Name, args: Seq[H.Atom]) => {
        val f = Symbol.fresh("f")
        val rewrittenFun = rewrite(fun)(_substitutions)
        L.LetP(f, CPSV.BlockGet, Seq(rewrittenFun, 0),
               L.AppF(f, retC, rewrittenFun +: args.map(rewrite(_)(_substitutions))))
      }
      // arithmetics
      // +
      case H.LetP(n: H.Name, L3.IntAdd, Seq(x: H.Atom, y: H.Atom), b: H.Body) =>
        tmpLetP(CPSV.XOr, Seq(rewrite(x)(_substitutions), 1), {
          _x => L.LetP(n, CPSV.Add, Seq(_x, rewrite(y)(_substitutions)), h2lVal(b)(_substitutions))
        })
      // TODO: change (- 1) to (XOR 1) to clear LSB
      // -
      case H.LetP(n: H.Name, L3.IntSub, Seq(x: H.Atom, y: H.Atom), b: H.Body) =>
        tmpLetP(CPSV.Sub, Seq(rewrite(x)(_substitutions), rewrite(y)(_substitutions)), {
          _x => L.LetP(n, CPSV.Add, Seq(_x, 1), h2lVal(b)(_substitutions))
        })
      // ×
      case H.LetP(n: H.Name, L3.IntMul, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.Sub, Seq(rewrite(x)(_substitutions), 1), {
          _x => tmpLetP(CPSV.ShiftRight, Seq(rewrite(y)(_substitutions), 1), {
            _y => tmpLetP(CPSV.Mul, Seq(_x, _y), {
              z => L.LetP(n, CPSV.Add, Seq(z, 1), h2lVal(b)(_substitutions))
            })
          })
        })
      }
      // ÷
      // ⟦n ÷ m⟧ = 2 × ( (⟦n⟧ - 1) / (⟦m⟧ - 1) ) + 1
      case H.LetP(n: H.Name, L3.IntDiv, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.Sub, Seq(rewrite(x)(_substitutions), 1), {
          _x => tmpLetP(CPSV.Sub, Seq(rewrite(y)(_substitutions), 1), {
            _y => tmpLetP(CPSV.Div, Seq(_x, _y), {
              z => tmpLetP(CPSV.Mul, Seq(z, 2), {
                z2 => L.LetP(n, CPSV.Add, Seq(z2, 1), h2lVal(b)(_substitutions))
              })
            })
          })
        })
      }
      // %
      // ⟦n MOD m⟧ = (⟦n⟧ - 1 MOD ⟦m⟧ - 1) + 1
      case H.LetP(n: H.Name, L3.IntMod, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.Sub, Seq(rewrite(x)(_substitutions), 1), {
          _x => tmpLetP(CPSV.Sub, Seq(rewrite(y)(_substitutions), 1), {
            _y => tmpLetP(CPSV.Mod, Seq(_x, _y), {
              z => L.LetP(n, CPSV.Add, Seq(z, 1), h2lVal(b)(_substitutions))
            })
          })
        })
      }
      // <<
      case H.LetP(n: H.Name, L3.IntShiftLeft, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.Sub, Seq(rewrite(x)(_substitutions), 1), {
          _x => tmpLetP(CPSV.ShiftRight, Seq(rewrite(y)(_substitutions), 1), { // Right-shifting ⟦y⟧ already clears LSB.
            _y => tmpLetP(CPSV.ShiftLeft, Seq(_x, _y), {
              z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b)(_substitutions)) // equivalent to adding 1
            })
          })
        })
      }
      // >>
      case H.LetP(n: H.Name, L3.IntShiftRight, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(y)(_substitutions), 1), {
          _y => tmpLetP(CPSV.ShiftRight, Seq(rewrite(x)(_substitutions), _y), {
            z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b)(_substitutions))
          })
        })
      }
      // &
      case H.LetP(n: H.Name, L3.IntBitwiseAnd, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        L.LetP(n, CPSV.And, Seq(rewrite(x)(_substitutions), rewrite(y)(_substitutions)), h2lVal(b)(_substitutions))
      }
      // |
      case H.LetP(n: H.Name, L3.IntBitwiseOr, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        L.LetP(n, CPSV.Or, Seq(rewrite(x)(_substitutions), rewrite(y)(_substitutions)), h2lVal(b)(_substitutions))
      }
      // ^
      case H.LetP(n: H.Name, L3.IntBitwiseXOr, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
        tmpLetP(CPSV.XOr, Seq(rewrite(x)(_substitutions), rewrite(y)(_substitutions)), {
          z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b)(_substitutions))
        })
      }
      // id
      case H.LetP(n: H.Name, L3.Id, Seq(a: H.Atom), b: H.Body) => {
        L.LetP(n, CPSV.Id, Seq(rewrite(a)(_substitutions)), h2lVal(b)(_substitutions))
      }
      // Comparison
      // <
      case H.If(L3.IntLt, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
        L.If(CPST.Lt, args.map(rewrite(_)(_substitutions)), thenC, elseC)
      // ≤
      case H.If(L3.IntLe, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
        L.If(CPST.Le, args.map(rewrite(_)(_substitutions)), thenC, elseC)
      // =
      case H.If(L3.Eq, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
        L.If(CPST.Eq, args.map(rewrite(_)(_substitutions)), thenC, elseC)
      // Type check
      // int?
      case H.If(L3.IntP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
        tmpLetP(CPSV.And, Seq(rewrite(a)(_substitutions), 1), {
          t1 => L.If(CPST.Eq, Seq(t1, 1), thenC, elseC)
        })
      // block?
      case H.If(L3.BlockP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
        tmpLetP(CPSV.And, Seq(rewrite(a)(_substitutions), 0x3), {
          t1 => L.If(CPST.Eq, Seq(t1, 0), thenC, elseC)
        })
      // char?
      case H.If(L3.CharP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
        tmpLetP(CPSV.And, Seq(rewrite(a)(_substitutions), 0x7), {
          t1 => L.If(CPST.Eq, Seq(t1, 6), thenC, elseC)
        })
      // bool?
      case H.If(L3.BoolP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) => 
        tmpLetP(CPSV.And, Seq(rewrite(a)(_substitutions), 0xF), {
          t1 => L.If(CPST.Eq, Seq(t1, 10), thenC, elseC)
        })
      // unit?
      case H.If(L3.UnitP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
        tmpLetP(CPSV.And, Seq(rewrite(a)(_substitutions), 0xF), {
          t1 => L.If(CPST.Eq, Seq(t1, 2), thenC, elseC)
        })
      // block operations
      // block-alloc
      case H.LetP(n: H.Name, L3.BlockAlloc, Seq(a1, a2), body: H.Body) => {
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(a1)(_substitutions), 1), {
          t1 => tmpLetP(CPSV.ShiftRight, Seq(rewrite(a2)(_substitutions), 1), {
            t2 => L.LetP(n, CPSV.BlockAlloc, Seq(t1, t2), h2lVal(body)(_substitutions))
          })
        })
      }
      // block-tag
      case H.LetP(n: H.Name, L3.BlockTag, Seq(a: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.BlockTag, Seq(rewrite(a)(_substitutions)), {
          t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
            t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body)(_substitutions))
          })
        })
      // block-length
      case H.LetP(n: H.Name, L3.BlockLength, Seq(a: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.BlockLength, Seq(rewrite(a)(_substitutions)), {
          t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
            t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body)(_substitutions))
          })
        })
      // block-get
      case H.LetP(n: H.Name, L3.BlockGet, Seq(b: H.Atom, i: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(i)(_substitutions), 1), {
          _i => L.LetP(n, CPSV.BlockGet, Seq(rewrite(b)(_substitutions), _i), h2lVal(body)(_substitutions)) // need to untag returned element?
        })
      // block-set!
      case H.LetP(n: H.Name, L3.BlockSet, Seq(b: H.Atom, i: H.Atom, v: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(i)(_substitutions), 1), {
          _i => L.LetP(n, CPSV.BlockSet, Seq(rewrite(b)(_substitutions), _i, rewrite(v)(_substitutions)), h2lVal(body)(_substitutions))
        })
      // I/O
      // byte-read
      case H.LetP(n: H.Name, L3.ByteRead, Seq(), body: H.Body) =>
        tmpLetP(CPSV.ByteRead, Seq.empty[L.Atom], {
          t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
            t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body)(_substitutions))
          })
        })
      // byte-write
      case H.LetP(n: H.Name, L3.ByteWrite, Seq(a: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(a)(_substitutions), 1), {
          t1 => L.LetP(n, CPSV.ByteWrite, Seq(t1), h2lVal(body)(_substitutions))
        })
      // integer and character conversion
      // char->int
      case H.LetP(n: H.Name, L3.CharToInt, Seq(a: H.Atom), body: H.Body) =>
        L.LetP(n, CPSV.ShiftRight, Seq(rewrite(a)(_substitutions), 2), h2lVal(body)(_substitutions))
      // int->char
      case H.LetP(n: H.Name, L3.IntToChar, Seq(a: H.Atom), body: H.Body) =>
        tmpLetP(CPSV.ShiftLeft, Seq(rewrite(a)(_substitutions), 2), {
          t1 => L.LetP(n, CPSV.Or, Seq(t1, 0x2), h2lVal(body)(_substitutions))
        })
      // halt
      case H.Halt(arg: H.Atom) => 
        tmpLetP(CPSV.ShiftRight, Seq(rewrite(arg)(_substitutions), 1), {
          _a => L.Halt(_a)
        })
    }
  }
  
  private def rewrite(a: H.Atom)(substitutions: Subst[Symbol]): L.Atom = a match {
    case n: H.Name     => substitutions(n)
    case IntLit(v)     => (v.toInt << 1) | 1 // equivalent to `v * 2 + 1`
    case CharLit(c)    => (c.toInt << 3) | 6 // 0b110
    case BooleanLit(b) => if (b) 0x1A else 0xA
    case UnitLit       => 0x2
  }

  private def tmpLetP(p: L.ValuePrimitive, args: Seq[L.Atom],
                      body: L.Name => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("t")
    L.LetP(tmp, p, args, body(tmp))
  }

  //private def h2lFun()

  private def fv(tree: H.Tree): Set[Symbol] = tree match {
    case H.LetP(n: H.Name, _, args: Seq[H.Atom], b: H.Body) =>
      (fv(b) excl n) union args.map(fvAtom(_)).fold(Set.empty[Symbol])(_ union _)
    case H.LetC(cnts: Seq[H.Cnt], body: H.Body) =>
      fv(body) union cnts.map {
        case H.Cnt(_, args: Seq[H.Name], e: H.Body) =>
          fv(e) diff args.toSet
      }.fold(Set.empty[Symbol])(_ union _)
    case H.LetF(funs: Seq[H.Fun], body: H.Body) =>
      fv(body) union funs.map {
        case H.Fun(_, _ ,args: Seq[H.Name], e: H.Body) =>
          fv(e) diff args.toSet
      }.fold(Set.empty[Symbol])(_ union _) diff funs.map(_.name).toSet // Must `diff` lie on the same line as operands?
    case H.AppC(_, args: Seq[H.Atom]) =>
      args.map(fvAtom(_)).fold(Set.empty[Symbol])(_ union _)
    case H.AppF(fun: H.Atom, _, args: Seq[H.Atom]) =>
      fvAtom(fun) union args.map(fvAtom(_)).fold(Set.empty[Symbol])(_ union _)
    case H.If(_, args: Seq[H.Atom], _, _) =>
      args.map(fvAtom(_)).fold(Set.empty[Symbol])(_ union _)
    case H.Halt(a: H.Atom) =>
      fvAtom(a)
  }

  private def fvAtom(a: H.Atom): Set[Symbol] = a match {
    case n: H.Name => Set(n)
    case l: H.Literal => Set.empty
  }
}
