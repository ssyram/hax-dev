#!/bin/bash

# Check if an argument is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <coq|fstar|json|all>"
    exit 1
fi

# Set the environment variable
export RUSTFLAGS="-C instrument-coverage"

# Function to run the command for a given feature
run_cargo_hax() {
    local feature=$1
    echo "Running tests for $feature..."
    
    # Handle json case differently (no 'into' command)
    if [ "$feature" == "json" ]; then
        cargo hax -C --features "$feature" \; $feature
    else
        cargo hax -C --features "$feature" \; into "$feature"
    fi
}

# Select the appropriate action based on the input argument
case "$1" in
    coq)
        run_cargo_hax "coq"
        ;;
    fstar)
        run_cargo_hax "fstar"
        ;;
    json)
        run_cargo_hax "json"
        ;;
    all)
        run_cargo_hax "json" && \
        run_cargo_hax "fstar" && \
        run_cargo_hax "coq"
        ;;
    *)
        echo "Invalid argument. Please use one of the following: coq, fstar, json, all"
        exit 1
        ;;
esac
