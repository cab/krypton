plugins {
    `java-library`
}

dependencies {
    implementation(project(":runtime"))
}

tasks.jar {
    archiveBaseName.set("krypton-repl")
}
