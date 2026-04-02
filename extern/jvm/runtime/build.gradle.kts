plugins {
    `java-library`
}

dependencies {
    api("com.fasterxml.jackson.core:jackson-databind:2.18.2")
}

tasks.jar {
    archiveBaseName.set("krypton-runtime")
    from(configurations.runtimeClasspath.get().map { if (it.isDirectory()) it else zipTree(it) })
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
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

tasks.named("check") {
    dependsOn(noSynchronized)
}
