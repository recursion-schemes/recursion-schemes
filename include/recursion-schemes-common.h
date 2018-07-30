#ifndef MIN_VERSION_base
#define MIN_VERSION_base(x,y,z) 1
#endif

#ifndef MIN_VERSION_transformers
#define MIN_VERSION_tarnsformers(x,y,z) 1
#endif

#ifndef MIN_VERSION_transformers_compat
#define MIN_VERSION_transformers_compat(x,y,z) 0
#endif


#if MIN_VERSION_base(4,9,0)
#define LIFTED_FUNCTOR_CLASSES 1

#elif MIN_VERSION_transformers(0,5,0)
#define LIFTED_FUNCTOR_CLASSES 1

#elif MIN_VERSION_transformers_compat(0,5,0) && !MIN_VERSION_transformers(0,4,0)
#define LIFTED_FUNCTOR_CLASSES 1
#endif


#define HAS_GENERIC (__GLASGOW_HASKELL__ >= 702)
#define HAS_GENERIC1 (__GLASGOW_HASKELL__ >= 706)

#define HAS_POLY_TYPEABLE MIN_VERSION_base(4,7,0)
