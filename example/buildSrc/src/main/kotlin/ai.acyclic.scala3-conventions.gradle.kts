plugins {

    id("ai.acyclic.scala-mixin")
    id("io.github.cosmicsilence.scalafix")
}

val vs = versions()

allprojects {

    dependencies {

        bothImpl("org.scala-lang:scala3-library_3:${vs.scala.v}")
        bothImpl("org.scala-lang:scala3-staging_3:${vs.scala.v}")
    }

    tasks {

        withType<ScalaCompile> {

            scalaCompileOptions.apply {

                additionalParameters.addAll(
                    listOf(
//                        "-verbose"
                        "-explain",

                        "-experimental",
                        "-feature",

//                        "-rewrite",
//                        "-source:future-migration",
                        "-source:future",

//                        "-language:experimental.modularity",
                        "-explain-cyclic",

                        "-Wunused:all",// demand by scalafix

//                        "-language:experimental.dependent"

//                        "-verbose", // enable in case of compiler bug
//                        "-Ydebug",
                    )
                )
            }
        }
    }
}
