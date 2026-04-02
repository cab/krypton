plugins {
    base
}

subprojects {
    repositories {
        mavenCentral()
    }

    plugins.withId("java") {
        extensions.configure<JavaPluginExtension> {
            toolchain {
                languageVersion = JavaLanguageVersion.of(21)
            }
        }

        extensions.configure<TestingExtension> {
            suites {
                named<JvmTestSuite>("test") {
                    useJUnitJupiter("5.11.4")
                }
            }
        }

        tasks.withType<Test>().configureEach {
            jvmArgs("-Djdk.tracePinnedThreads=short")
        }
    }
}

tasks.named("assemble") {
    dependsOn(":runtime:assemble", ":repl:assemble")
}

tasks.named("check") {
    dependsOn(":runtime:check", ":repl:check")
}

val test by tasks.registering {
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    description = "Run the JVM runtime and REPL test suites."
    dependsOn(":runtime:test", ":repl:test")
}
