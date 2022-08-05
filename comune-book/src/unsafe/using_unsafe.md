# Using `unsafe`

There are various features in Comune, often carried over from C/C++, that are marked as `unsafe`:
- Declaring, and operating on, raw pointers


There are also several default behaviours that can be `unsafe`ly overridden:
- A class with virtual functions must have a virtual destructor
- 