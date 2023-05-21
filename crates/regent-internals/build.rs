// SPDX-License-Identifier: MPL-2.0

use rustc_version::{Channel, version_meta};

fn main() {
    if std::env::var_os("REGENT_NO_NIGHTLY").is_some() {
        return;
    }

    let meta = version_meta().unwrap();
    if !matches!(meta.channel, Channel::Nightly) {
        return;
    }

    // Enable the `nightly` feature.
    println!("cargo:rustc-cfg=feature=\"nightly\"");
}
