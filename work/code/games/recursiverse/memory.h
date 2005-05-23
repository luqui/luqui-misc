#ifndef __MEMORY_H__
#define __MEMORY_H__

const size_t pool_size = 256;
typedef unsigned char byte;

class FixedPool
{
public:
    FixedPool(size_t size);
    FixedPool(size_t size, void* buf);   // for a preallocated buffer
    ~FixedPool();

    void* allocate();
    void free(void* mem);
    
    void* head_mem() { return (void*)data; }
    int bytes() { return object_size * pool_size; }
    int slots() { return slots_remaining; }
    bool contains(void* mem) { return (byte*)mem - data >= 0 && 
                                      (byte*)mem - data < bytes(); }
    
private:
    void init_pool();
    
    const size_t object_size;
    int slots_remaining;

    bool external_buffer;
    byte head;
    byte* data;
};

FixedPool::FixedPool(size_t size)
    : object_size(size), slots_remaining(pool_size), head(0), 
      external_buffer(false)
{
    data = new byte[object_size * pool_size];
    init_pool();
}

FixedPool::FixedPool(size_t size, void* buf)
    : object_size(size), slots_remaining(pool_size), head(0), 
      data((byte*)buf), external_buffer(true)
{
    init_pool();
}

FixedPool::~FixedPool()
{
    if (!external_buffer) {
        delete[] data;
    }
}

void FixedPool::init_pool()
{
    // make a circularly-linked list out of our unused data
    for (size_t i = 0; i < pool_size-1; i++) {
        data[i * object_size] = i+1;
    }
    data[object_size * (pool_size - 1)] = 0;
}

inline void* FixedPool::allocate()
{
    int offs = head * object_size;
    head = data[offs];
    slots_remaining--;
    return (void*)&data[offs];
}

inline void FixedPool::free(void* mem)
{
    int offs = ((byte*)mem - data);
    byte pos = offs / object_size;
    data[offs] = head;
    head = pos;
    slots_remaining++;
}



class PoolChain
{
public:
    PoolChain(size_t size);
    ~PoolChain();

    void* allocate();
    void free(void* mem);

private:
    const size_t object_size;
    
    struct PoolList
    {
        PoolList* next;
        FixedPool* pool;
    };

    PoolList* head;

    FixedPool* new_pool();
};

PoolChain::PoolChain(size_t size)
    : object_size(size), head(0)
{ }

PoolChain::~PoolChain()
{
    PoolList* cptr = head;
    while (cptr) {
        PoolList* next = cptr->next;
        delete cptr;
        cptr = next;
    }
}

void* PoolChain::allocate()
{
    if (head) {
        if (head->pool->slots()) {
            return head->pool->allocate();
        }
       
        PoolList* last = head;
        PoolList* cptr = head->next;
        while (cptr) {
            if (cptr->pool->slots()) {
                // we found one; bring this pool to the front
                // so that it will be recovered quickly
                last->next = cptr->next;
                cptr->next = head;
                head = cptr;
                return cptr->pool->allocate();
            }
            last = cptr;
            cptr = cptr->next;
        }
    }

    // either we don't have a head, or all of our pools are full
    // in either case, we need a new pool
    return new_pool()->allocate();
}

void PoolChain::free(void* mem)
{
    PoolList* cptr = head;
    while (cptr) {
        if (cptr->pool->contains(mem)) {
            cptr->pool->free(mem);
            return;
        }
        cptr = cptr->next;
    }
	DIE("Cannot find allocated memory pool");
}

FixedPool* PoolChain::new_pool()
{
    PoolList* newlist = new PoolList;
    newlist->pool = new FixedPool(object_size);
    newlist->next = head;
    head = newlist;
    return newlist->pool;
}


const int max_small_object_size = 64;

class Allocator
{
public:
    Allocator();

    void* allocate(size_t size);
    void free(void* mem, size_t size);
    
private:
    PoolChain* chains[max_small_object_size];
};

Allocator::Allocator()
{
    chains[0] = 0;   // we deserve to die if they try to allocate 0 bytes
    for (size_t i = 1; i < max_small_object_size; i++) {
        chains[i] = new PoolChain(i);
    }
}

inline void* Allocator::allocate(size_t size)
{
    if (size < max_small_object_size) {
        return chains[size]->allocate();
    }
    else {
        return ::operator new(size);
    }
}

inline void Allocator::free(void* mem, size_t size)
{
    if (size < max_small_object_size) {
        chains[size]->free(mem);
    }
    else {
        ::operator delete(mem);
    }
}


Allocator g_Allocator;

class SmallObject
{
public:
    virtual ~SmallObject() { }
    
#ifdef USE_SMALL_OBJECT_POOLS
    void* operator new (size_t size) {
        return g_Allocator.allocate(size);
    }

    void* operator new (size_t size, void* place) {
        return place;  // placement new knows what he's doing
    }

    void operator delete (void* mem, size_t size) {
        g_Allocator.free(mem, size);
    }
#endif
};


// an int* wrapper so we can make use of SmallObject
struct refct : public SmallObject
{
    refct(int in) : ct(in) { }
    int ct;
};

template <class T>
class ptr : public SmallObject
{
public:
    ptr() : ref(0), ct(0) { }
    
    ptr(T* in) : ref(in), ct(in ? new refct(1) : 0) { }
    
    ptr(const ptr& in) : ref(in.ref), ct(in.ct) { if (ct) ct->ct++; }
    
    template <class U>
    ptr(const ptr<U>& in) : ref(in.ref), ct(in.ct) { if (ct) ct->ct++; }

    ~ptr() { release(); }

    template <class U>
    ptr& operator = (const ptr<U>& in) {
        if (in.ref == ref)
            return *this;
        release();
        ref = in.ref;
        ct = in.ct;
        if (ct) ct->ct++;
        return *this;
    }

    template <class U>
    ptr& operator = (U* in) {
        if (ref == in)
            return *this;
        release();
        if (!in) {
            ref = 0;
            ct = 0;
        }
        else {
            ref = in;
            ct = new refct(1);
        }
        return *this;
    }

    T& operator * () const {
        return *ref;
    }

    T* operator -> () const {
        return ref;
    }

    bool null() const {
        return !ref;
    }

private:
    template <class U>
    friend class ptr;
    
    void release() {
        if (ct && !--ct->ct) {
            delete ref;
            delete ct;
        }
    }
    
    T* ref;
    refct* ct;
};

#endif
