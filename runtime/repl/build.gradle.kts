plugins {
    `java-library`
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(rootProject)
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(21)
    }
}

tasks.jar {
    archiveBaseName.set("krypton-repl")
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useJUnitJupiter("5.11.4")
        }
    }
}
