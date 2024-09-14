**Formal verification on CNN Accelerator**
1. Temporal behavior
   - Check whether the computation finishes within the required cycle.
   - Check whether the loading cycle and computation cycle taken each time for each tiled data have a regular value with respect to the dimension of system and network size.
2. Equivalence property
   - Check the answer of each layer and the final network result.
3. Safety property
    - Check whether the overflow of the MAC units happens during the computation.
    - Check whether the data overlapping happens during the communication and storing of the partial data.
    - Check whether the FIFO in the output buﬀer overflows.
