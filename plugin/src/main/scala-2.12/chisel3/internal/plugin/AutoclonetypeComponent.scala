// SPDX-License-Identifier: Apache-2.0

package chisel3.internal.plugin

import scala.collection.mutable
import scala.tools.nsc
import scala.tools.nsc.{Global, Phase}
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.TypingTransformers

// TODO rename, this could be BundleComponent or something
// We could change how Bundles determine their elements, instead having this component implement it
// This drew heavily from https://github.com/alexarchambault/data-class which is Apache 2.0 licensed
private[plugin] class AutoclonetypeComponent(val global: Global) extends PluginComponent with TypingTransformers {
  import global._

  val phaseName: String = "chiselautoclonetype"
  val runsAfter: List[String] = List[String]("typer")
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
    val bundleTpe = inferType(tq"chisel3.Bundle")

    def isBundle(sym: Symbol): Boolean =
      sym.fullName == "chisel3.Bundle" || sym.parentSymbolsIterator.exists(isBundle)

    def isAbstract(mods: Modifiers): Boolean = mods.hasFlag(Flag.ABSTRACT)

    def isAccessor(mods: Modifiers): Boolean = mods.hasAccessorFlag

    def collectPublicVals(body: List[Tree]): Seq[Int] = {
      val allFields = mutable.ListBuffer[ValDef]()
      val paramAccessors = mutable.ListBuffer[ValDef]()
      val accessors = mutable.ListBuffer[DefDef]()
      val constructors = mutable.ListBuffer[DefDef]()
      body.foreach {
        case field: ValDef =>
          allFields += field
          if (field.mods.hasFlag(Flag.PARAMACCESSOR)) {
            paramAccessors += field
          }
        case accessor: DefDef if accessor.mods.hasAccessorFlag => accessors += accessor
        //case constructor: DefDef if constructor.mods.hasFlag
        case _ =>
      }
      println(s"allFields = ${allFields.map(_.name)}")
      println(s"paramAccessors = ${paramAccessors.map(_.name)}")
      println(s"accessors = ${accessors.map(_.name)}")
      List(1)
    }

    override def transform(tree: Tree): Tree = tree match {
      case bundle: ClassDef if isBundle(bundle.symbol) =>
        // This is the only way I can figure out how to get paramss
        val q"""$mods class $tpname[..$tparams] $ctorMods(...$paramss)
                       extends { ..$earlydefns } with ..$parents { $self =>
                         ..$stats
            }""" = bundle
        val paramssTyped = paramss.asInstanceOf[List[List[ValDef]]]
        val tparamsTyped = tparams.asInstanceOf[List[TypeDef]]
        val allParams = paramssTyped.flatten
        val body: List[Tree] = stats.asInstanceOf[List[Tree]]

        println(s"========== Matched on $tpname ==========")
        println(s"tparamsTyped = $tparamsTyped")
        val hasCloneType = body.exists {
          case d @ DefDef(_, nme, tparams, vparamss, _, _)
            if nme.decodedName.toString == "cloneType" && tparams.isEmpty && vparamss.isEmpty =>
            global.reporter.warning(d.pos, "The Chisel compiler plugin now implements cloneType")
            true
          case _ => false
        }
        def mkCloneType = {
          val paramssRefs = paramssTyped.map(_.map(_.name))
          val tparamsRefs = tparamsTyped.map { t => tq"${t.name}" }
          val impl = q"override def cloneType: $tpname.this.type = new $tpname[..$tparamsRefs](...$paramssRefs)"
          localTyper.typed(impl)
        }
        if (!hasCloneType) {
          // Despite the q""" """" above, this is the only way I can figure out how to add the method
          val ClassDef(mods0, name0, tparams0, template @ Template(parents0, self0, body0)) = bundle
          val templateResult = treeCopy.Template(template, parents0, self0, body0 :+ mkCloneType)
          treeCopy.ClassDef(bundle, mods0, name0, tparams0, templateResult)
        } else {
          super.transform(tree)
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
        val publicVals = collectPublicVals(body)
        println(s"publicVals = $publicVals")

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