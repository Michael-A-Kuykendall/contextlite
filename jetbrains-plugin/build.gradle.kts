plugins {
    id("java")
    id("org.jetbrains.kotlin.jvm") version "1.9.10"
    id("org.jetbrains.intellij") version "1.15.0"
}

group = "com.contextlite"
version = "1.0.0"

repositories {
    mavenCentral()
}

// Configure Gradle IntelliJ Plugin
intellij {
    version.set("2023.1.5")
    type.set("IC") // Target IDE Platform
    
    plugins.set(listOf(/* Plugin Dependencies */))
}

dependencies {
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
    testImplementation("junit:junit:4.13.2")
}

tasks {
    // Set the JVM compatibility versions
    withType<JavaCompile> {
        sourceCompatibility = "17"
        targetCompatibility = "17"
    }
    
    withType<org.jetbrains.kotlin.gradle.tasks.KotlinCompile> {
        kotlinOptions.jvmTarget = "17"
    }

    patchPluginXml {
        sinceBuild.set("231")
        untilBuild.set("241.*")
        
        changeNotes.set("""
            <h3>1.0.0</h3>
            <ul>
                <li>Initial release of ContextLite IntelliJ plugin</li>
                <li>Start/stop ContextLite server from IDE</li>
                <li>Auto-detect ContextLite binary installation</li>
                <li>Status indicator in status bar</li>
                <li>Quick access via Tools menu</li>
            </ul>
        """.trimIndent())
    }

    signPlugin {
        certificateChain.set(System.getenv("CERTIFICATE_CHAIN"))
        privateKey.set(System.getenv("PRIVATE_KEY"))
        password.set(System.getenv("PRIVATE_KEY_PASSWORD"))
    }

    publishPlugin {
        token.set(System.getenv("PUBLISH_TOKEN"))
        channels.set(listOf("stable"))
    }
    
    buildSearchableOptions {
        enabled = false
    }
}
