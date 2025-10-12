import org.gradle.api.Project
import org.gradle.api.artifacts.dsl.DependencyHandler

/**
 * Configures the current project as a Kotlin project by adding the Kotlin `stdlib` as a dependency.
 */
fun Project.versions(): Versions {

    return Versions(this)
}

// see https://github.com/gradle/gradle/issues/13067
fun DependencyHandler.bothImpl(dependencyNotation: Any): Unit {
    // TODO: https://stackoverflow.com/questions/77512791/in-gradle-kotlinscript-dsl-how-to-import-generated-class-accessors-like-implem
    add("implementation", dependencyNotation)
    add("testFixturesImplementation", dependencyNotation)
}


fun getModuleID_Scala(project: Project): String {
    val rootVersions = project.rootProject.versions()

    val suffix = "_" + rootVersions.scala.binaryV
    val moduleID = rootVersions.rootID + project.path.replace(':', '-') + suffix

    return moduleID
}