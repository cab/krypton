plugins {
    `java-library`
}

repositories {
    mavenCentral()
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(21)
    }
}

tasks.jar {
    archiveBaseName.set("krypton-runtime")
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useJUnitJupiter("5.11.4")
        }
    }
}

tasks.withType<Test> {
    jvmArgs("-Djdk.tracePinnedThreads=short")
}

val noSynchronized by tasks.registering {
    description = "Fail if production source uses 'synchronized' (pins virtual threads)"
    doLast {
        val violations = fileTree("src/main/java") {
            include("**/*.java")
        }.files.filter { it.readText().contains("synchronized") }
        if (violations.isNotEmpty()) {
            throw GradleException(
                "synchronized keyword found — use ReentrantLock instead:\n" +
                violations.joinToString("\n") { "  ${it.relativeTo(projectDir)}" }
            )
        }
    }
}

tasks.named("check") { dependsOn(noSynchronized) }
