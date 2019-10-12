from setuptools import setup

setup(
    name='reamit',
    version='0.1.0',
    description='Readable assembly code generator',
    url='https://github.com/matthewscholefield/reamit',
    author='Matthew D. Scholefield',
    author_email='matthew331199@gmail.com',
    classifiers=[
        'Development Status :: 3 - Alpha',

        'Intended Audience :: Developers',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
        'Programming Language :: Python :: 3.6',
    ],
    keywords='reamit',
    packages=['reamit'],
    install_requires=[],
    entry_points={
        'console_scripts': [
            'reamit=reamit.__main__:main'
        ],
    }
)
