use std::{fs, process::Command};

// Run a command with arguments and a working directory, and ensure it succeeds.
fn run_command(command: &str, args: &[&str], dir: &str) -> std::process::ExitStatus {
    Command::new(command)
        .args(args)
        .current_dir(dir)
        .status()
        .expect("Failed to start process")
}

fn configure() {
    let configure = run_command(
        "./configure.sh",
        &["--auto-download", "--cocoa"],
        "./cvc5",
    );
    assert!(configure.success(), "Configuration failed");
}

fn build() {
    let build = run_command("make", &[], "./cvc5/build");
    assert!(build.success(), "Building failed");
}

fn install() {
    let install = run_command("make", &["install"], "./cvc5/build");
    assert!(install.success(), "Installation failed");
}

fn move_cvc5() {
    fs::rename(
        "./cvc5/build/bin/cvc5",
        "./src/cvc5",
    )
    .expect("Failed to move the cvc5 binary");
}

fn main() {
    configure();
    build();
    install();
    move_cvc5();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::tempdir;

    #[test]
    fn test_run_command() {
        let echo = run_command("echo", &["Hello, World!"], ".");
        assert!(echo.success());
    }

    #[test]
    #[ignore]
    /// Not run by default as it takes a long time.
    /// Can configure the cvc5 binary.
    fn test_configure() {
        let configure = run_command(
            "./configure.sh",
            &[
                "--prefix=/usr/local",
                "--name=./build",
                "--auto-download",
                "--cocoa",
            ],
            "./cvc5",
        );
        assert!(configure.success(), "Configuration failed");
    }

    #[test]
    #[ignore]
    /// Not run by default as it takes a long time.
    /// Can build the cvc5 binary.
    fn test_build() {
        let build = run_command("make", &[], "./cvc5/build");
        assert!(build.success(), "Building failed");
    }

    #[test]
    #[ignore]
    /// Not run by default as it takes a long time.
    /// Can install the cvc5 binary.
    fn test_install() {
        let install = run_command("make", &["install"], "./cvc5/build");
        assert!(install.success(), "Installation failed");
    }

    #[test]
    fn test_move_cvc5() {
        // Create a temporary directory.
        let dir = tempdir().expect("Failed to create temporary directory");

        // Create a dummy cvc5 binary in the temporary directory.
        let cvc5_path = dir.path().join("cvc5");
        fs::File::create(&cvc5_path)
            .expect("Failed to create cvc5 binary")
            .write_all(b"dummy content")
            .expect("Failed to write to cvc5 binary");

        // Create a target directory.
        let target_dir = dir.path().join("circomference/src");
        fs::create_dir_all(&target_dir).expect("Failed to create target directory");

        // Move the cvc5 binary to the target directory.
        fs::rename(&cvc5_path, target_dir.join("cvc5")).expect("Failed to move cvc5 binary");

        // Ensure that the cvc5 binary is now in the target directory.
        assert!(
            target_dir.join("cvc5").exists(),
            "cvc5 binary was not moved"
        );

        // Clean up the temporary directory.
        dir.close().expect("Failed to clean up temporary directory");
    }
}
