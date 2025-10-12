buildscript {
    repositories {
        mavenCentral()
    }
    dependencies {
        classpath("ch.epfl.scala:gradle-bloop_2.12:1.6.4") // suffix is always 2.12, weird
    }
}


plugins {
    id("ai.acyclic.scala3-conventions")
}

idea {

    module {
//        excludeDirs.add(file("latex"))
    }
}