import React from 'react'

import profilePic from './me4.jpeg'

export default function Bio() {
  return (
    <div
      style={{ display: 'flex' }}
    >
      <img
        src={profilePic}
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
        <strong>Joel Burget</strong>
        cofounder{' '}
      </p>
    </div>
  )
}
