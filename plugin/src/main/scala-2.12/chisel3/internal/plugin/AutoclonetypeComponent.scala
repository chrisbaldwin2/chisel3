// SPDX-License-Identifier: Apache-2.0

package chisel3.internal.plugin

import scala.collection.mutable
import scala.tools.nsc
import scala.tools.nsc.{Global, Phase}
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.symtab.Flags
import scala.tools.nsc.transform.TypingTransformers
import scala.util.Failure

// TODO rename, this could be BundleComponent or something
// We could change how Bundles determine their elements, instead having this component implement it
// This drew heavily from https://github.com/alexarchambault/data-class which is Apache 2.0 licensed
private[plugin] class AutoclonetypeComponent(val global: Global) extends PluginComponent with TypingTransformers {
  import global._

  val phaseName: String = "chiselautoclonetype"
  val runsAfter: List[String] = "typer" :: Nil
  def newPhase(prev: Phase): Phase = new AutoclonetypePhase(prev)

  private class AutoclonetypePhase(prev: Phase) extends StdPhase(prev) {
    override def name: String = phaseName
    def apply(unit: CompilationUnit): Unit = {
      // This plugin doesn't work on Scala 2.11. Rather than complicate the sbt build flow,
      // instead we just check the version and if its an early Scala version, the plugin does nothing
      if (scala.util.Properties.versionNumberString.split('.')(1).toInt >= 12) {
        unit.body = new MyTypingTransformer(unit).transform(unit.body)
      }
    }
  }


  private class MyTypingTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    def inferType(t: Tree): Type = localTyper.typed(t, nsc.Mode.TYPEmode).tpe
    //val bundleTpe = inferType(tq"chisel3.Bundle")

    def isBundle(sym: Symbol): Boolean = {
      sym.fullName == "chisel3.Bundle" || sym.parentSymbolsIterator.exists(isBundle)
    }

    def isAbstract(mods: Modifiers): Boolean = mods.hasFlag(Flag.ABSTRACT)

    def isAccessor(mods: Modifiers): Boolean = mods.hasAccessorFlag

    def getParamsAndConstructor(body: List[Tree]): (Option[DefDef], Seq[Symbol]) = {
      val paramAccessors = mutable.ListBuffer[Symbol]()
      var primaryConstructor: Option[DefDef] = None
      body.foreach {
        case acc if acc.symbol.isParamAccessor =>
          paramAccessors += acc.symbol
        case con: DefDef if con.symbol.isPrimaryConstructor =>
          primaryConstructor = Some(con)
        case d @ DefDef(_, nme, tparams, vparamss, _, _)
          if nme.decodedName.toString == "cloneType" && tparams.isEmpty && vparamss.isEmpty =>
          global.reporter.warning(d.pos, "The Chisel compiler plugin now implements cloneType")
        case _ =>
      }
      (primaryConstructor, paramAccessors.toList)
    }

    private def showRawAll(any: Any): String =
      showRaw(any, true, true, true, true, true, true) //printTypes, printIds, printOwners, printKinds, printMirrors, printPositions)

    override def transform(tree: Tree): Tree = tree match {

      case bundle: ClassDef if isBundle(bundle.symbol) =>
        bundle match {
          case q"""$mods class $tpname[..$tparams] $ctorMods(...$paramss)
                       extends { ..$earlydefns } with ..$parents { $self =>
                         ..$stats
            }""" =>
            println(s"========== Matched on ${bundle.symbol} ==========")
            println(bundle)

            val (con, params) = getParamsAndConstructor(bundle.impl.body)
            val constructor = con.getOrElse {
              global.globalError(bundle.pos, "Unable to determine primary constructor!");
              ???
            }
            //val `this` = //This(bundle.symbol)
            val thiz = gen.mkAttributedThis(bundle.symbol)

            // Create a this.<ref> for each field matching order of constructor arguments
            val conArgs: List[List[RefTree]] =
              constructor.vparamss.map(_.map { vp =>
                params.collectFirst {
                  case p if vp.name == p.name => gen.mkAttributedSelect(thiz, p)
                }.get
              })
            val thisDotType = bundle.symbol.thisType
            // Note, the created New() object seems to have an incomplete TypeTree,
            // TODO check if this is right
            // This TypeTree is just trying to match what hand-written override cloneType gives, it's weird
            //val ttpe = TypeTree(bundle.symbol.tpe).setOriginal(gen.mkAttributedIdent(bundle.symbol))
            //val ttpe = bundle.symbol.tpe
            val ttpe = Ident(bundle.symbol)
            val neww = localTyper.typed(New(ttpe, conArgs))

            /*
            // The below is not quite right, it's `new MyBundle.<init>(...)` instead of `new MyBundle(...)`
            val neww = localTyper.typed(if (conArgs.nonEmpty) {
              conArgs.tail.foldLeft(gen.mkMethodCall(constructor.symbol, conArgs.head)) {
                case (meth, args) => gen.mkMethodCall(meth, args)
              }
            } else {
              gen.mkMethodCall(constructor.symbol, Nil)
            })

             */


            // Now we need to cast .asInstanceOf[this.type]
            //val rhs = gen.mkAttributedCast(neww, thisDotType)
            val rhs0 = gen.mkAttributedCast(neww, thisDotType)
            // FIXME rhs0 and rhs seem to give same bytecode, but rhs matches showRaw of hand-written better
            // NOTE neither work
            val rhs = rhs0 match {
              case TypeApply(fun, _) =>
                val tpeName = bundle.symbol.tpe.typeSymbol.name.asInstanceOf[TypeName]
                TypeApply(fun, List(TypeTree(thisDotType).setOriginal(SingletonTypeTree(This(tpeName)))))
            }


            //val cloneTypeSym =  bundle.symbol.newMethod(TermName("cloneType"), bundle.symbol.pos.focus, Flag.OVERRIDE)
            val cloneTypeSym =  bundle.symbol.newMethod(TermName("_cloneTypeImpl"), bundle.symbol.pos.focus, Flag.OVERRIDE)
            //cloneTypeSym.flags = Flag.OVERRIDE
            cloneTypeSym.resetFlag(Flags.METHOD)
            //cloneTypeSym.setInfo(thisDotType)
            cloneTypeSym.setInfo(NullaryMethodType(thisDotType))
            println(s"cloneTypeSym = $cloneTypeSym, ${cloneTypeSym.info} :: ${showRaw(cloneTypeSym, printIds=true)}")

            // TODO do we need to clear info or anything?
            //val defdef = DefDef(Modifiers(Flag.OVERRIDE), TermName("cloneType"), Nil, Nil, TypeTree(thisDotType), rhs)
            val defdef = localTyper.typed(DefDef(cloneTypeSym, rhs))

            println(s"===== Plugin Generated =====")
            //println(s"New = ${showRaw(New(bundle.symbol.tpe), printIds=true, printOwners=true, printKinds=true)} or ${showRaw(localTyper.typed(New(bundle.symbol.tpe)), printIds=true, printOwners=true, printKinds=true)}")
            println(defdef)
            //println(showRaw(defdef, printIds=true, printOwners=true, printKinds=true))
            println(showRawAll(defdef))
            println(s"Symbol.info: ${defdef.symbol.info.getClass} = ${showRaw(defdef.symbol.info)}")
            println(showRaw(defdef.symbol, printIds=true, printOwners=true, printKinds=true))

            val cloneTypes = bundle.impl.body.collect { case d: DefDef if d.name.toString == "cloneType" => d }
            cloneTypes match {
              case Seq() => // Do nothing
              case Seq(cloneType) =>
                assert(cloneTypes.size == 1, "BAD")
                val cloneType = cloneTypes.head
                println(s"===== From Source =====")
                println(cloneType)
                //println(showRaw(cloneType, printIds = true, printOwners = true, printKinds = true))
                println(showRawAll(cloneType))
                println(s"Symbol info: ${cloneType.symbol.info.getClass} = ${showRaw(cloneType.symbol.info)}")
                println(showRaw(cloneType.symbol, printIds = true, printOwners = true, printKinds = true))
                println(s"====================")
                println("Same structure? " + cloneType.equalsStructure(defdef))

                defdef match {
                  case DefDef(_, _, _, _, _, rhs0@TypeApply(_, args0)) =>
                    cloneType match {
                      case DefDef(_, _, _, _, _, rhs1@TypeApply(_, args1)) =>
                        println(s"Args heads structure? " + args0.head.equalsStructure(args1.head))
                      case _ => ???
                    }
                  case _ => ???
                }
              case many => throw new Exception("BAD")
            }

            val method = localTyper.typed(defdef)
            val withMethod = deriveClassDef(bundle) { t =>
              deriveTemplate(t)(_ :+ method)
            }
            //if (cloneTypes.nonEmpty) super.transform(bundle)
            //else localTyper.typed(withMethod)
            val res = localTyper.typed(withMethod)
            //println("OWNER = " + res.symbol.owner)
            //println(showRaw(res, printIds = true, printOwners = true))
            res
            //super.transform(bundle)

          // Some classes don't match the quasiquotes above
          case other => super.transform(other)
        }



      case bundle: ClassDef if isBundle(bundle.symbol) =>
        // This is the only way I can figure out how to get paramss
        //println(s"========== Outer match on ${bundle.symbol} ==========")
        //println(bundle)
        bundle match {
          case q"""$mods class $tpname[..$tparams] $ctorMods(...$paramss)
                       extends { ..$earlydefns } with ..$parents { $self =>
                         ..$stats
               }""" =>

            val paramssTyped = paramss.asInstanceOf[List[List[ValDef]]]
            val tparamsTyped = tparams.asInstanceOf[List[TypeDef]]
            val allParams = paramssTyped.flatten
            val body: List[Tree] = stats.asInstanceOf[List[Tree]]

            println(s"========== Matched on $tpname ==========")
            println(bundle)
            //println(s"tparamsTyped = $tparamsTyped")
            val hasCloneType = body.exists {
              case d @ DefDef(_, nme, tparams, vparamss, _, _)
                if nme.decodedName.toString == "cloneType" && tparams.isEmpty && vparamss.isEmpty =>
                global.reporter.warning(d.pos, "The Chisel compiler plugin now implements cloneType")
                println(showRaw(d, printTypes=true, printIds=true))

                true
              case _ => false
            }
            mkCloneType

            def mkCloneType: Option[Tree] = scala.util.Try {
              val `this` = This(bundle.impl.symbol.owner)
              val paramssRefs = paramssTyped.map(_.map(p => Select(`this`, p.name)))
              val tparamsRefs = tparamsTyped.map { t => tq"${t.name}" }
              val thisDotType = TypeTree().setOriginal(SingletonTypeTree(`this`))
              //val thisDotType = SingletonTypeTree(This(tpname))
              //val impl = q"override def cloneType: $tpname.this.type = new $tpname[..$tparamsRefs](...$paramssRefs);"
              val impl = q"override def cloneType = new ${bundle.symbol}[..$tparamsRefs](...$paramssRefs).asInstanceOf[$thisDotType]"
              //impl setType NoType
              println(s"impl  = $impl")
              println(showRaw(impl, printTypes =true))

              println("===== Jack =====")
              val foo = gen.mkAttributedSelect(`this`, paramssTyped.head.head.symbol)
              println(s"typing '$foo'...")
              val bar = localTyper.typed(foo)
              println(bar)
              println(showRaw(bar, printTypes=true))
              println("================")
              /*
              impl match {
                case d @ DefDef(mods, nme, tparams, vparamss, tpt, rhs) =>
                  println(s"mods = $mods, nme = $nme, tparams = $tparams, vparams = $vparamss, tpt = $tpt, rhs = $rhs")
                  rhs match {
                    case Apply(fun, args) =>
                      println(s"Apply fun = $fun, args = $args")
                      fun match {
                        case Apply(fun2, args2) =>
                          println(s"fun2 = $fun2, args2 = $args2")
                          fun2 match {
                            case Select(qual, name3) =>
                              println(s"qual = $qual: ${qual.getClass}, name3 = $name3")
                          }
                          /*fun2 match {
                            case 
                          }*/
                      }
                  }
              }
               */
              val term = TermName("cloneType")
              val mods = Modifiers(Flag.OVERRIDE)
              //DefDef(mods, term, Nil, Nil, TypeTree(), )
              //val rhs: Tree = null
              //val impl2 = DefDef(nme, mods, paramss, rhs)

              //localTyper.namer.enterDefDef(impl.asInstanceOf[DefDef])
              //println(s"named = $impl")

              val res = localTyper.typed(impl)
              //val res = localTyper.typedDefDef(impl.asInstanceOf[DefDef])
              // val res = impl
              println("B")
              res
            }.recoverWith {
              case x =>
                println(s"Failed with $x")
                Failure(x)
            }.toOption

            //val x: Symbol = gen
            //gen.mkMethodCall()
            paramssTyped.head.head.symbol

            if (hasCloneType) {
              // Have already warned at the definition of cloneType
              super.transform(tree)
            } else mkCloneType match {
              case Some(cloneType) =>
                // Despite the q""" """" above, this is the only way I can figure out how to add the method
                println(s"===== From =====")
                println(bundle)
                val ClassDef(mods0, name0, tparams0, template@Template(parents0, self0, body0)) = bundle
                println("A")
                val templateRes = treeCopy.Template(template, parents0, self0, body0 :+ cloneType)
                println(templateRes)
                val templateResult = localTyper.typed(templateRes).asInstanceOf[Template]
                println("templateResult = " + templateResult)
                println("C")
                val result = treeCopy.ClassDef(bundle, mods0, name0, tparams0, templateResult)
                println(s"===== To =====")
                println(result)
                val typedResult = localTyper.typed(result)
                println(s"===== Typed =====")
                println(typedResult)
                //super.transform(result)
                super.transform(typedResult)
              case None =>
                // FIXME can we fix this case?
                global.reporter.warning(bundle.pos, "Unable to generate cloneType")
                super.transform(tree)
            }
          case _ => println(s"$bundle does not match"); super.transform(tree)
        }
      case bundle @ ClassDef(mods, name, tparams, impl) if isBundle(bundle.symbol) =>
        //d.symbol
        println(s"========== Matched on $name ==========")
        val abs = isAbstract(mods)
        println(s"abstract = $abs")
        val body = impl match {
          case Template(parents, self, body) =>
            println(s"parents = $parents")
            println(s"self = $self")
            println(s"body = $body")
            body
        }
        println(s"children = ${bundle.children}")
        //val publicVals = collectPublicVals(body)
        //println(s"publicVals = $publicVals")

        super.transform(tree)
      /*
      case d @ q"""$mods class $tpname[..$tparams] $ctorMods(...$paramss)
                      extends { ..$earlydefns } with ..$parents { $self =>
                  ..$stats
            }""" =>
        val subtypeOfBundle = isABundle(d.symbol)
        println(s"********** Matched on $tpname ? $subtypeOfBundle **********")
        if (subtypeOfBundle) {
          println(stats)
        }
        super.transform(tree)
       */
      case _ => super.transform(tree)
    }
  }
}