import React from 'react'
import styled from 'react-emotion';

import joelJpg from './joel.jpg'
import brianJpg from './brian.jpg'

const bios = {
  joel: JoelBio,
  brian: BrianBio,
};

const BiosWrapper = styled.div`
  display: flex;
`;

const BioWrapper = styled.div`
  display: flex;
  margin-right: 50px;
`;

export default function Bios({ names }) {
  return (
    <BiosWrapper>
      {names.map(name => bios[name]())}
    </BiosWrapper>
  );
}

function JoelBio() {
  return (
    <BioWrapper>
      <img
        src={joelJpg}
        alt="Joel Burget"
        style={{
          marginBottom: 0,
          width: "100px",
          height: "100px",
          borderRadius: "50%",
        }}
      />
      <p
        style={{
          display: 'flex',
          flexDirection: 'column',
          justifyContent: 'center',
          marginLeft: 25,
        }}
      >
        <strong><a href="https://twitter.com/dino_joel">Joel Burget</a></strong>
        cofounder{' '}
      </p>
    </BioWrapper>
  )
}

function BrianBio() {
  return (
    <BioWrapper>
      <img
        src={brianJpg}
        alt="Brian Schroeder"
        style={{
          marginBottom: 0,
          width: "100px",
          height: "100px",
          borderRadius: "50%",
        }}
      />
      <p
        style={{
          display: 'flex',
          flexDirection: 'column',
          justifyContent: 'center',
          marginLeft: 25,
        }}
      >
        <strong><a href="https://twitter.com/bschroed">Brian Schroeder</a></strong>
        cofounder{' '}
      </p>
    </BioWrapper>
  )
}
