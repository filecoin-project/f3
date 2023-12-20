# F3 (Fast Finality Filecoin) PlusCal/TLA+ spec

Currently, the Filecoin Expected Consensus protocol offers only probabilistic finality. By convention, a tipset 900 epochs old (approximately 7.5h) is considered "final", based on a protocol parameter that determines the longest fork that a node will consider re-organising.

The long time to finality considerably hinders the user experience and limits applications built on Filecoin, and the fact that finality is only probabilistic is a significant risk to any external effects or cross-chain transactions. 

The goal of the F3 project is to introduce deterministic finality with low latency, equaling 1 epoch on expectation. 

## Project details

Refer to the [F3 Indexer](https://docs.google.com/document/d/10IE6hfK16dbrH9lPWlPS7vGcFRRTAtYzjXEEeYhdkek/edit#heading=h.7u0l42ugupr9) for additional information and links.

## This repository

This repository stores a PlusCal/TLA+ specification for GossiPBFT.
