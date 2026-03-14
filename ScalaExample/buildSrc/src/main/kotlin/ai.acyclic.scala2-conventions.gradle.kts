plugins {

    id("ai.acyclic.scala-mixin")
}

val vs = versions()

allprojects {

    dependencies {

        bothImpl("${vs.scala.group}:scala-library:${vs.scala.v}")
        bothImpl("${vs.scala.group}:scala-reflect:${vs.scala.v}")
//        bothImpl("${vs.scala.group}:scala-compiler:${vs.scala.v}") // enable if low-level mutli-stage programming is required


        if (vs.splainV.isNotEmpty()) {
            val splainD = "io.tryp:splain_${vs.scala.v}:${vs.splainV}"
            logger.warn("using ${splainD} ...\t in ${project.displayName} / scalaCompilerPlugins")

            scalaCompilerPlugins(splainD)
        }
    }

    tasks {

        withType<ScalaCompile> {

            scalaCompileOptions.apply {

                additionalParameters.addAll(
                    listOf(
                        "-deprecation",
                        "-unchecked",
                        "-feature",
                        "-language:higherKinds",
                        "-language:existentials",


//                        "-Vtyper",

                        "-g:vars", // demand by json4s
                        "-Ywarn-unused",// demand by scalafix
//                        "-Ywarn-value-discard",

                        "-Wconf:cat=unused-params:i,cat=unused-locals:i",
                        // see:
                        // https://www.scala-lang.org/2021/01/12/configuring-and-suppressing-warnings.html

//                        "-Wconf:cat=other-pure-statement:ws",
//                        "-Wconf:cat=other-pure-statement:ws&site=.*Macro.*:s",

                        "-Xlint:poly-implicit-overload",
                        "-Xlint:option-implicit",

//                        "-verbose", // enable in case of compiler bug
//                        "-Ydebug",

                    )
                )

                if (vs.splainV.isNotEmpty()) {
                    additionalParameters.addAll(
                        listOf(
                            "-Vimplicits", "-Vimplicits-verbose-tree", "-Vtype-diffs",
                            "-P:splain:Vimplicits-diverging",
                            "-P:splain:Vtype-detail:4",
                            "-P:splain:Vtype-diffs-detail:3",
//                            "-P:splain:Vdebug"
                        )
                    )
                }
            }
        }
    }
}
