# RESTRICTER Code (Early Version)

## Prerequisites
- Python 3.8 or higher

## Installation

We interface with the cedar engine in rust using two custom python packages, which are only available as pre-built wheels for x86_64 Linux right now. We will provide the source code along with building instructions soon.

Install the packages "cedar2json-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl" and "cedarpy-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl" using pip on a virtual environment:
```bash
python3 -m venv venv
source venv/bin/activate
pip install cedar2json-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
pip install cedarpy-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
```

Also install the cvc5 package:
```bash
pip install cvc5==1.2.0
```

## Example Usage

An example run:
```bash
python3 restricter-case-study-gclass.py --size 50 --slice 0 --entities_prefix gclassroom_2026_entities --log_prefix gclassroom_2026_logs
```
Will run RESTRICTER on the classroom management case study where the entity store json is at `gclassroom_2026_entities.50.json`, and the log is at `gclassroom_2026_logs.50.json`. We run RESTRICTER on only one rule (rule 0).

## Structure

```
.
├── README.md
├── cedar2json-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
├── cedarpy-0.2.0-cp38-abi3-manylinux_2_34_x86_64.whl
├── gclassroom.cedar
├── gclassroom.schema.json
├── gclassroom_2026_entities.50.json
├── gclassroom_2026_logs.50.json
├── get_pt.py
├── parse_schema.py
├── restricter-case-study-gclass.py
├── translate_entity_store.py
└── util.py
```

`restricter-case-study-gclass.py` is the script that runs the classroom management case study, which contains the main algorithm of RESTRICTER.

`gclassroom.cedar` and `gclassroom.schema.json` are the Cedar policy and schema files for the classroom management case study.

`gclassroom_2026_entities.50.json` and `gclassroom_2026_logs.50.json` are example entity store and log files for the case study.

`translate_entity_store.py` contains the main function that interfaces with SyGuS to do rule tightening.

`get_pt.py` contains the function that picks a request from the potential over-privilege set.
