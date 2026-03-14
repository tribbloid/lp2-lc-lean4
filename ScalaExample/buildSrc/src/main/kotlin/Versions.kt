import org.gradle.api.JavaVersion
import org.gradle.api.Project

class Versions(private val rootProject: Project) {

    // TODO : how to group them?
    val rootGroup = rootProject.properties["rootGroup"]?.toString() ?: "ai.acyclic"

    val rootID = rootProject.properties["rootID"]?.toString() ?: "scaffold"

    val rootGroupID = "$rootGroup.$rootID"

    val rootV = rootProject.properties["rootVersion"]?.toString() ?: "1.0.0-SNAPSHOT"
    val rootVMajor = rootV.removeSuffix("-SNAPSHOT")

    inner class Scala {
        val group: String = rootProject.properties["scalaGroup"]?.toString() ?: "org.scala-lang"

        val v: String = rootProject.properties["scalaVersion"].toString()
        protected val vParts: List<String> = v.split('.').also { parts ->
            require(parts.size == 3) { "Scala version must be in format 'X.Y.Z' but was: $v" }
        }

        val majorV: String = vParts[0]
        val binaryV: String = vParts.subList(0, 2).joinToString(".")
        val patchV: String = vParts[2]

        val artifactSuffix = run {
            if (majorV == "3") majorV
            else binaryV
        }
    }

    val scala: Scala by lazy { Scala() }

    val javaVersion = rootProject.properties["javaVersion"]?.toString()?.let { JavaVersion.toVersion(it) }
        ?: JavaVersion.VERSION_17

    val jvmTarget = javaVersion

    val scalaTestV = "3.2.19"
    val splainV: String = rootProject.properties["splainVersion"]?.toString() ?: ""

    val scalajsV: String? = rootProject.properties.get("scalaJSVersion")?.toString()


    inner class Spark {

        val v: String = rootProject.properties["sparkVersion"].toString()
        protected val vParts: List<String> = v.split('.')

        val majorV: String = vParts[0]
        val binaryV: String = vParts.subList(0, 2).joinToString(".")
        val patchV: String = vParts[2]
    }

    val spark: Spark by lazy { Spark() }
}
