from SMT2UnsignedMultiplierData import SMT2UnsignedMultiplierData

def main():
    test = SMT2UnsignedMultiplierData(3)
    print test.generate_proof()

if __name__ == '__main__':
    main()
