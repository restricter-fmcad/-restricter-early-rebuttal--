# RESTRICTER Code (Early Version)

## Prerequisites
- Python 3.8 or higher
- cvc5 package

## Installation
Install the packages "cedar2json-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl" and "cedarpy-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl" using pip on a virtual environment:
```bash
python3 -m venv venv
source venv/bin/activate
pip install cedar2json-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
pip install cedarpy-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
```

## Structure

`restricter-case-study-gclass.py` is the script that runs the classroom management case study, which contains the main algorithm of RESTRICTER.

`translate_entity_store.py` contains the main function that interfaces with SyGuS to do rule tightening.

`get_pt.py` contains the function that picks a request from the potential over-privilege set.