# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "cp",
    srcs = ["src/main.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/cp_lib",
        "//sw/host/provisioning/ujson_lib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
    ],
)
