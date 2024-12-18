#!/bin/bash

set -e

echo "Building Expreduce kernel..."
go build -o expreduce_for_jupyter

# Set the virtual environment directory
VENV_DIR="venv"

# Check if the virtual environment exists
if [ ! -d "$VENV_DIR" ]; then
  echo "Creating virtual environment..."
  python3 -m venv "$VENV_DIR"
fi

# Activate the virtual environment
source "$VENV_DIR/bin/activate"

# Upgrade pip
echo "Upgrading pip..."
pip install --upgrade pip

pip install nbclassic

# Install Jupyter if not already installed
if ! pip show jupyter > /dev/null 2>&1; then
  echo "Installing Jupyter..."
  pip install notebook
fi

pip install setuptools

pip install metakernel --upgrade

# TODO(corywalker): Switch back to upstream once pull requests are merged.
[ -d "iwolfram" ] || git clone https://github.com/corywalker/iwolfram.git
cd iwolfram
python setup.py install --mma-exec ../expreduce_for_jupyter

# Run Jupyter Notebook
echo "Starting Jupyter Notebook..."
jupyter notebook --ip=0.0.0.0 --port=8888 --no-browser

# Deactivate the virtual environment on exit
deactivate
