# 1-Update Protocol

*1-Update* is a new cache coherence protocol ... A brief description follows and more details can be found in the [PACT'21](http://pact21.snu.ac.kr/) paper. 

This is the publicly available artifact repository supporting *1-Update*, which contains the formal protocol specification. The specification is written in TLA+ and can be used to verify 1-Update's correctness via model-checking.

TODO
---- 

## Model checking
To model check 1-Update, you need to download and install the TLA+ Toolbox so that you can run the *TLC* model checker using the *TLA+* specification. We next list the steps for model checking.
* __Prerequisites__: Any OS with Java 1.8 or later, to accommodate the *TLA+* Toolbox.
* __Download and install__ the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
* __Launch__ the TLA+ Toolbox.
* __Create a spec__: *File>Open Spec>Add New Spec...*; Browse and use *1Update/OneUpdate.tla* as root module to finish.
* __Create a new Model__: Navigate to *TLC Model Checker>New model...*; and create a model with the name "one-update-model".
* __Setup Behavior__: In *Model Overview* tab of the model, and under the *"What is the behavior spec?"* section, select *"Temporal formula"* and write *"Spec"*.
* __Setup Constants__: Then specify the values of declared constants (under *"What is the model?"* section). You may use low values for constants to check correctness without exploding the state space. An example configuration would be three cores and maximum writes of two or three. To accomplish that, you would need to click on each constant and select the "ordinary assignment" option. Then fill the box for version and epoch constants (e.g., *MAX_WRITES*) with a small number (e.g., with *"3"* or *"4"*) and for the core related fields (e.g., *CORES*) with a set of cores (e.g., *"{1,2,3}"* -- for three cores).

### File Structure
* __The 1-Update specification__ is decoupled into two modules folder for simplicity. *OneUpdate.tla* and *OneUpdateMeta.tla*.

#### Caveats 
* 

----
### License
This work is freely distributed under the [Apache 2.0 License](https://www.apache.org/licenses/LICENSE-2.0 "Apache 2.0").  

### Contact
 Antonios Katsarakis: <a href="http://antonis.io/" title="Personal webpage" target="_blank">`antonis.io`</a> |  [`antoniskatsarakis@yahoo.com`](mailto:antoniskatsarakis@yahoo.com?subject=[GitHub]%20Zeus%20Specification "Email")
