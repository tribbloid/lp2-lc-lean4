plugins {
    `kotlin-dsl`
}

repositories {
    mavenLocal()
    mavenCentral()
    gradlePluginPortal() // so that external plugins can be resolved in dependencies section
}

dependencies {
    implementation("com.github.ben-manes.versions:com.github.ben-manes.versions.gradle.plugin:0.51.0")
    implementation("io.github.gradle-nexus.publish-plugin:io.github.gradle-nexus.publish-plugin.gradle.plugin:1.3.0")
    implementation("io.github.cosmicsilence.scalafix:io.github.cosmicsilence.scalafix.gradle.plugin:0.2.3")
}
