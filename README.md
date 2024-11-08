# simple-tla-checker

Bare-bones interpreter & model-checker for a subset of the TLA+ language for the purpose of experimenting with bytecode interpretation.

## Build

This project uses Java 11, so install [JDK 11 or later](https://adoptopenjdk.net/releases.html).

This project uses the [Gradle](https://gradle.org/) build system for Java; however, installing Gradle is not necessary due to the way Gradle works.
Running the scripts below downloads a pinned Gradle version then uses it to execute the build.

On Linux and macOS, run `./gradlew build`

On Windows, run `.\gradlew.bat build`

## Run

Run `./gradlew run --args="Test.tla"`

You can edit [`app/Test.tla`](app/Test.tla) to change program behavior.
Note that the program is run from the `app` directory, so all relative paths will need to be from there.

